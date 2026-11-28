// The JavaScript model derivation and semantic hash as they were before the verified kernel
// (WG-4799): src/core/parse.js and the normalize/hash part of src/core/hash.js, kept unchanged as
// a differential oracle. tests/proofs/model-kernel.test.js compares the Lean kernel, called through
// src/core/parse.js and src/core/hash.js, with it on every specification the tests use. Like the
// Rust engine for the simulator, it is not used by the application.


import { parseTree, getNodeValue, printParseErrorCode } from 'jsonc-parser';
import metamodel from '../../src/core/metamodel.json' with { type: 'json' };
import { CLAIM_METHODS } from '../../src/core/claim-methods.js';
import { own } from '../../src/core/own.js';

/** @typedef {import('../../src/core/types.js').Model} Model */
/** @typedef {import('../../src/core/types.js').Entity} Entity */
/** @typedef {import('../../src/core/types.js').Diagnostic} Diagnostic */
/** @typedef {import('../../src/core/types.js').Loc} Loc */

export const SCHEMA_VERSION = metamodel.schemaVersion;
export const BASE_METAMODEL = metamodel;
/** A ref whose allowed kinds contain this may point to an entity of any kind, including kinds a specification declares. */
export const ANY_KIND = '*';
const ID_RE = new RegExp(metamodel.idPattern);

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

/**
 * Build the effective meta-model: the built-in one plus the specification's
 * vocabulary (extra categories, relationship kinds and entity properties).
 * @param {any} vocab plain value of the `vocabulary` section (may be undefined)
 * @param {(code:string, message:string, path:(string|number)[]) => void} report
 */
function effectiveMeta(vocab, report) {
  /** @type {any} */
  const meta = {
    entities: structuredClone(metamodel.entities),
    categories: structuredClone(metamodel.vocabulary.categories),
    relationshipKinds: structuredClone(metamodel.vocabulary.relationshipKinds),
    projections: [...metamodel.vocabulary.projections],
    sections: structuredClone(metamodel.sections),
    /** @type {Record<string, {label: string, description: string}>} */
    verificationMethods: {},
  };
  if (vocab === undefined) return meta;
  if (!isObject(vocab)) { report('vocabulary.type', '"vocabulary" must be an object.', ['vocabulary']); return meta; }
  for (const key of Object.keys(vocab)) {
    if (!['categories', 'relationshipKinds', 'properties', 'entityKinds', 'verificationMethods'].includes(key)) {
      report('vocabulary.unknown', `Unsupported vocabulary section "${key}".`, ['vocabulary', key]);
    }
  }
  const V = metamodel.vocabulary;
  if (vocab.categories !== undefined) {
    if (!isObject(vocab.categories)) report('vocabulary.type', '"vocabulary.categories" must be an object keyed by category id.', ['vocabulary', 'categories']);
    else for (const [id, def] of Object.entries(vocab.categories)) {
      const p = ['vocabulary', 'categories', id];
      if (!isObject(def)) { report('vocabulary.type', `Category "${id}" must be an object.`, p); continue; }
      const d = /** @type {any} */ (def);
      for (const k of Object.keys(d)) if (!['label', 'shape', 'color', 'description'].includes(k)) report('vocabulary.unknown', `Unsupported category field "${k}".`, [...p, k]);
      if (typeof d.label !== 'string') report('vocabulary.type', `Category "${id}" needs a string "label".`, p);
      if (!V.shapes.includes(d.shape)) report('vocabulary.shape', `Category "${id}" needs "shape" to be one of: ${V.shapes.join(', ')}.`, p);
      if (!V.colors.includes(d.color)) report('vocabulary.color', `Category "${id}" needs "color" to be one of: ${V.colors.join(', ')}.`, p);
      meta.categories[id] = { label: String(d.label ?? id), shape: V.shapes.includes(d.shape) ? d.shape : 'box', color: V.colors.includes(d.color) ? d.color : 'slate', description: typeof d.description === 'string' ? d.description : '', declared: true };
    }
  }
  if (vocab.relationshipKinds !== undefined) {
    if (!isObject(vocab.relationshipKinds)) report('vocabulary.type', '"vocabulary.relationshipKinds" must be an object keyed by kind id.', ['vocabulary', 'relationshipKinds']);
    else for (const [id, def] of Object.entries(vocab.relationshipKinds)) {
      const p = ['vocabulary', 'relationshipKinds', id];
      if (!isObject(def)) { report('vocabulary.type', `Relationship kind "${id}" must be an object.`, p); continue; }
      const d = /** @type {any} */ (def);
      for (const k of Object.keys(d)) if (!['label', 'line', 'color', 'dependency', 'description', 'class', 'direction', 'parent'].includes(k)) report('vocabulary.unknown', `Unsupported relationship kind field "${k}".`, [...p, k]);
      if (typeof d.label !== 'string') report('vocabulary.type', `Relationship kind "${id}" needs a string "label".`, p);
      if (!V.lines.includes(d.line)) report('vocabulary.line', `Relationship kind "${id}" needs "line" to be one of: ${V.lines.join(', ')}.`, p);
      if (!V.colors.includes(d.color)) report('vocabulary.color', `Relationship kind "${id}" needs "color" to be one of: ${V.colors.join(', ')}.`, p);
      if (d.class === undefined && typeof d.dependency !== 'boolean') report('vocabulary.type', `Relationship kind "${id}" needs a boolean "dependency".`, p);
      const taxonomy = Object.fromEntries(['class', 'direction', 'parent'].filter((k) => d[k] !== undefined).map((k) => [k, d[k]]));
      meta.relationshipKinds[id] = { label: String(d.label ?? id), line: V.lines.includes(d.line) ? d.line : 'solid', color: V.colors.includes(d.color) ? d.color : 'neutral', dependency: d.class === undefined ? d.dependency === true : d.class !== 'none', description: typeof d.description === 'string' ? d.description : '', ...taxonomy, declared: true };
    }
  }
  /**
   * Turn a declared property into a meta-model property definition, or report why not.
   * Scalars, enums, references and lists of scalars or references are allowed.
   * @param {any} d @param {(string|number)[]} p @returns {any|null}
   */
  const propertyDef = (d, p) => {
    const scalar = ['string', 'text', 'boolean', 'number'];
    /** @param {any} x @param {boolean} inList @returns {any|null} */
    const typed = (x, inList) => {
      if (scalar.includes(x.type)) return { type: x.type };
      if (x.type === 'enum') {
        if (!(Array.isArray(x.values) && x.values.length && x.values.every((/** @type {any} */ v) => typeof v === 'string'))) { report('vocabulary.type', 'An enum property needs a non-empty string array "values".', p); return null; }
        return { type: 'enum', values: x.values };
      }
      if (x.type === 'ref') {
        const kinds = typeof x.ref === 'string' ? [x.ref] : x.ref;
        if (!(Array.isArray(kinds) && kinds.length && kinds.every((/** @type {any} */ k) => typeof k === 'string'))) { report('vocabulary.type', 'A ref property needs "ref": the entity kind(s) it may point to.', p); return null; }
        const unknown = kinds.filter((/** @type {string} */ k) => k !== ANY_KIND && !own(meta.entities, k));
        if (unknown.length) { report('vocabulary.entity', `Unknown entity kind(s) in "ref": ${unknown.join(', ')}.`, p); return null; }
        return { type: 'ref', ref: kinds };
      }
      if (x.type === 'list' && !inList) {
        if (!isObject(x.items)) { report('vocabulary.type', 'A list property needs "items": {"type": ...}.', p); return null; }
        const items = typed(x.items, true);
        return items ? { type: 'list', items } : null;
      }
      report('vocabulary.type', `Property type must be one of: ${[...scalar, 'enum', 'ref', 'list'].join(', ')}${inList ? ' (lists cannot nest)' : ''}.`, p);
      return null;
    };
    const base = typed(d, false);
    if (!base) return null;
    return { ...base, label: typeof d.label === 'string' ? d.label : undefined, doc: typeof d.doc === 'string' ? d.doc : undefined, required: d.required === true || undefined, expected: d.expected === true || undefined, extension: true };
  };
  const PROP_FIELDS = ['type', 'label', 'values', 'doc', 'expected', 'required', 'ref', 'items'];

  // Model-defined entity kinds: a specification may introduce its own kinds of
  // entity (goals, decisions, requirements, ...) with their properties and the
  // top-level section they are declared in.
  if (vocab.entityKinds !== undefined) {
    if (!isObject(vocab.entityKinds)) report('vocabulary.type', '"vocabulary.entityKinds" must be an object keyed by kind id.', ['vocabulary', 'entityKinds']);
    else {
      /** @type {[string, any, (string|number)[]][]} */
      const declared = [];
      for (const [id, def] of Object.entries(vocab.entityKinds)) {
        const p = ['vocabulary', 'entityKinds', id];
        if (!isObject(def)) { report('vocabulary.type', `Entity kind "${id}" must be an object.`, p); continue; }
        const d = /** @type {any} */ (def);
        for (const k of Object.keys(d)) if (!['label', 'section', 'doc', 'shape', 'color', 'properties'].includes(k)) report('vocabulary.unknown', `Unsupported entity kind field "${k}".`, [...p, k]);
        if (!/^[a-z][a-zA-Z0-9]*$/.test(id)) { report('vocabulary.type', `Entity kind id "${id}" must be alphanumeric and start with a lower-case letter.`, p); continue; }
        if (own(meta.entities, id)) { report('vocabulary.duplicate', `Entity kind "${id}" already exists.`, p); continue; }
        if (typeof d.label !== 'string' || !d.label) { report('vocabulary.type', `Entity kind "${id}" needs a string "label".`, p); continue; }
        if (typeof d.section !== 'string' || !/^[a-z][a-zA-Z0-9]*$/.test(d.section)) { report('vocabulary.type', `Entity kind "${id}" needs an alphanumeric "section" (the top-level key its entities are declared under).`, p); continue; }
        if (own(meta.sections, d.section)) { report('vocabulary.duplicate', `Section "${d.section}" is already in use.`, p); continue; }
        if (d.shape !== undefined && !V.shapes.includes(d.shape)) report('vocabulary.shape', `Entity kind "${id}": "shape" must be one of: ${V.shapes.join(', ')}.`, p);
        if (d.color !== undefined && !V.colors.includes(d.color)) report('vocabulary.color', `Entity kind "${id}": "color" must be one of: ${V.colors.join(', ')}.`, p);
        meta.entities[id] = {
          label: d.label, doc: typeof d.doc === 'string' ? d.doc : '', declared: true,
          shape: V.shapes.includes(d.shape) ? d.shape : 'box', color: V.colors.includes(d.color) ? d.color : 'neutral',
          properties: { id: { type: 'id', required: true } },
        };
        meta.sections[d.section] = { entity: id, declared: true };
        declared.push([id, d, p]);
      }
      // Properties second, so that kinds may refer to each other in any order.
      for (const [id, d, p] of declared) {
        if (d.properties === undefined) continue;
        if (!isObject(d.properties)) { report('vocabulary.type', `Entity kind "${id}": "properties" must be an object keyed by property name.`, p); continue; }
        for (const [name, pd] of Object.entries(d.properties)) {
          const pp = [...p, 'properties', name];
          if (!isObject(pd)) { report('vocabulary.type', `Property "${name}" must be an object.`, pp); continue; }
          if (!/^[a-zA-Z][a-zA-Z0-9]*$/.test(name) || name === 'id') { report('vocabulary.type', `Property name "${name}" must be alphanumeric and not "id".`, pp); continue; }
          for (const k of Object.keys(/** @type {any} */ (pd))) if (!PROP_FIELDS.includes(k)) report('vocabulary.unknown', `Unsupported property definition field "${k}".`, [...pp, k]);
          const built = propertyDef(pd, pp);
          if (built) meta.entities[id].properties[name] = { ...built, label: built.label ?? name, extension: undefined };
        }
      }
    }
  }

  if (vocab.properties !== undefined) {
    if (!Array.isArray(vocab.properties)) report('vocabulary.type', '"vocabulary.properties" must be an array.', ['vocabulary', 'properties']);
    else vocab.properties.forEach((/** @type {any} */ d, /** @type {number} */ i) => {
      const p = ['vocabulary', 'properties', i];
      if (!isObject(d)) { report('vocabulary.type', 'A property definition must be an object.', p); return; }
      for (const k of Object.keys(d)) if (!['entity', 'name', ...PROP_FIELDS].includes(k)) report('vocabulary.unknown', `Unsupported property definition field "${k}".`, [...p, k]);
      const ent = own(meta.entities, d.entity);
      if (!ent) { report('vocabulary.entity', `Unknown entity kind "${d.entity}" in property definition.`, p); return; }
      if (typeof d.name !== 'string' || !/^[a-zA-Z][a-zA-Z0-9]*$/.test(d.name)) { report('vocabulary.type', 'A property definition needs an alphanumeric "name".', p); return; }
      if (ent.properties[d.name]) { report('vocabulary.duplicate', `Property "${d.name}" already exists on ${d.entity}.`, p); return; }
      const built = propertyDef(d, p);
      if (built) ent.properties[d.name] = { ...built, label: built.label ?? d.name };
    });
  }

  // Verification methods that are carried out by tools outside Exegra. A claim
  // may name one; Exegra then reports only what recorded evidence says.
  if (vocab.verificationMethods !== undefined) {
    if (!isObject(vocab.verificationMethods)) report('vocabulary.type', '"vocabulary.verificationMethods" must be an object keyed by method id.', ['vocabulary', 'verificationMethods']);
    else for (const [id, def] of Object.entries(vocab.verificationMethods)) {
      const p = ['vocabulary', 'verificationMethods', id];
      const d = /** @type {any} */ (def);
      if (!isObject(d) || typeof d.label !== 'string') { report('vocabulary.type', `Verification method "${id}" must be an object with a string "label".`, p); continue; }
      for (const k of Object.keys(d)) if (!['label', 'description'].includes(k)) report('vocabulary.unknown', `Unsupported verification method field "${k}".`, [...p, k]);
      if (Object.hasOwn(CLAIM_METHODS, id)) { report('vocabulary.duplicate', `"${id}" is a built-in evaluation method.`, p); continue; }
      meta.verificationMethods[id] = { label: d.label, description: typeof d.description === 'string' ? d.description : '' };
    }
  }
  return meta;
}

/** @param {any} v */
function isObject(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }

/**
 * Parse specification source into a semantic model.
 * `model` is null only when the text is not syntactically usable.
 * Structural diagnostics are included; semantic rules live in validate.js.
 * @param {string} text
 * @returns {{model: Model|null, diagnostics: Diagnostic[]}}
 */
export function parseSpec(text) {
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
  if (root.type !== 'object') {
    diagnostics.push({ code: 'spec.root', severity: 'error', message: 'The specification must be a JSON object.', loc: locOf(starts, root.offset, root.length) });
    return { model: null, diagnostics };
  }

  /** @param {import('jsonc-parser').Node} node */
  const loc = (node) => locOf(starts, node.offset, node.length);
  /** @param {import('jsonc-parser').Node} obj */
  const members = (obj) => {
    /** @type {Map<string, {key: import('jsonc-parser').Node, value: import('jsonc-parser').Node}>} */
    const m = new Map();
    for (const prop of obj.children ?? []) {
      const [k, v] = prop.children ?? [];
      if (!k || !v) continue;
      if (m.has(k.value)) diagnostics.push({ code: 'property.duplicate', severity: 'error', message: `Property "${k.value}" is declared twice.`, loc: loc(k) });
      m.set(k.value, { key: k, value: v });
    }
    return m;
  };
  /** @param {(string|number)[]} path */
  const nodeAt = (path) => {
    /** @type {import('jsonc-parser').Node|undefined} */
    let n = root;
    for (const seg of path) {
      if (!n) return undefined;
      if (n.type === 'object') n = members(n).get(String(seg))?.value;
      else if (n.type === 'array') n = n.children?.[Number(seg)];
      else return undefined;
    }
    return n;
  };

  const top = members(root);
  const versionNode = top.get('exegra');
  if (!versionNode) diagnostics.push({ code: 'schema.missing', severity: 'error', message: `Missing "exegra" schema version (current: "${SCHEMA_VERSION}").`, loc: locOf(starts, root.offset, 1) });
  else if (versionNode.value.value !== SCHEMA_VERSION) diagnostics.push({ code: 'schema.version', severity: 'error', message: `Unsupported schema version ${JSON.stringify(versionNode.value.value)}; this build reads "${SCHEMA_VERSION}". Run "exegra migrate" if a migration exists.`, loc: loc(versionNode.value) });


  const vocabNode = top.get('vocabulary');
  const meta = effectiveMeta(vocabNode ? getNodeValue(vocabNode.value) : undefined, (code, message, path) => {
    const n = nodeAt(path) ?? vocabNode?.value ?? root;
    diagnostics.push({ code, severity: 'error', message, loc: loc(n), path });
  });

  for (const [key, m] of top) {
    if (!Object.hasOwn(meta.sections, key)) diagnostics.push({ code: 'spec.unknown-section', severity: 'error', message: `Unsupported top-level section "${key}".`, loc: loc(m.key), path: [key] });
  }

  /** @type {Model} */
  const model = {
    schemaVersion: SCHEMA_VERSION,
    system: /** @type {any} */ (null),
    entities: new Map(),
    byKind: {},
    refs: [],
    exprs: [],
    meta,
    vocabulary: vocabNode ? getNodeValue(vocabNode.value) : {},
  };
  for (const kind of Object.keys(meta.entities)) model.byKind[kind] = [];

  /**
   * @param {any} def property definition
   * @param {import('jsonc-parser').Node} node
   * @param {(string|number)[]} path
   * @param {string} ownerId entity that owns this value
   * @param {string} label for messages
   */
  const checkValue = (def, node, path, ownerId, label) => {
    /** @param {string} code @param {string} message */
    const bad = (code, message) => { diagnostics.push({ code, severity: 'error', message, loc: loc(node), path, entityId: ownerId }); };
    const t = def.type;
    switch (t) {
      case 'id': case 'string': case 'text':
        if (node.type !== 'string') bad('property.type', `${label} must be a string.`);
        return;
      case 'expr':
        if (node.type !== 'string') bad('property.type', `${label} must be an expression string.`);
        else model.exprs.push({ owner: ownerId, path, src: node.value, loc: loc(node) });
        return;
      case 'boolean':
        if (node.type !== 'boolean') bad('property.type', `${label} must be true or false.`);
        return;
      case 'number':
        if (node.type !== 'number') bad('property.type', `${label} must be a number.`);
        return;
      case 'enum': {
        const values = def.values ?? (def.valuesFrom === 'projections' ? meta.projections : Object.keys(own(meta, def.valuesFrom) ?? {}));
        if (node.type !== 'string' || !values.includes(node.value)) bad('property.enum', `${label} must be one of: ${values.join(', ')}.`);
        return;
      }
      case 'ref':
        if (node.type !== 'string') { bad('property.type', `${label} must be an entity id.`); return; }
        // A literal the definition allows in place of an id (the data model's "principal") is not a reference.
        if (Array.isArray(def.literals) && def.literals.includes(node.value)) return;
        model.refs.push({ from: ownerId, path, target: node.value, allowed: def.ref, loc: loc(node) });
        return;
      case 'list':
        if (node.type !== 'array') { bad('property.type', `${label} must be an array.`); return; }
        (node.children ?? []).forEach((child, i) => checkValue(def.items, child, [...path, i], ownerId, `${label}[${i}]`));
        return;
      case 'object':
        if (node.type !== 'object') { bad('property.type', `${label} must be an object.`); return; }
        checkFields(def.fields, node, path, ownerId, label);
        return;
      case 'map':
        if (node.type !== 'object') bad('property.type', `${label} must be an object.`);
        return;
      case 'effect': {
        // Shape is checked by validate.js; references and expressions are indexed here.
        if (node.type !== 'object') { bad('property.type', `${label} must be an object.`); return; }
        const m = members(node);
        const emit = m.get('emit')?.value;
        if (emit?.type === 'string') model.refs.push({ from: ownerId, path: [...path, 'emit'], target: emit.value, allowed: ['event'], loc: loc(emit) });
        const to = m.get('to')?.value;
        if (to?.type === 'string') model.exprs.push({ owner: ownerId, path: [...path, 'to'], src: to.value, loc: loc(to) });
        const payload = m.get('payload')?.value;
        if (payload?.type === 'object') for (const [k, e] of members(payload)) {
          if (e.value.type === 'string') model.exprs.push({ owner: ownerId, path: [...path, 'payload', k], src: e.value.value, loc: loc(e.value) });
        }
        return;
      }
      case 'evaluation': {
        if (node.type !== 'object') { bad('property.type', `${label} must be an object.`); return; }
        const m = members(node);
        const method = m.get('method')?.value;
        const mdef = method?.type === 'string' ? own(/** @type {any} */ (CLAIM_METHODS), method.value) : undefined;
        if (!mdef) return;
        /** @param {import('jsonc-parser').Node} n @param {(string|number)[]} p @param {string[]} allowed */
        const idRef = (n, p, allowed) => { if (n.type === 'string') model.refs.push({ from: ownerId, path: p, target: n.value, allowed, loc: loc(n) }); };
        /** @param {import('jsonc-parser').Node} n @param {(string|number)[]} p @param {string[]} allowed */
        const idRefs = (n, p, allowed) => {
          if (n.type === 'string') idRef(n, p, allowed);
          else if (n.type === 'array') (n.children ?? []).forEach((c, i) => idRef(c, [...p, i], allowed));
        };
        for (const [key, pdef] of Object.entries(mdef.params)) {
          const entry = m.get(key);
          if (!entry) continue;
          const type = /** @type {any} */ (pdef).type;
          const p = [...path, key];
          if (type === 'selector') {
            if (entry.value.type === 'object') {
              const sm = members(entry.value);
              const ids = sm.get('ids')?.value;
              if (ids) idRefs(ids, [...p, 'ids'], ['component']);
              const within = sm.get('within')?.value;
              if (within) idRef(within, [...p, 'within'], ['component']);
            } else idRefs(entry.value, p, ['component']);
          } else if (type.startsWith('ids:')) idRefs(entry.value, p, [type.slice(4)]);
          else if (type === 'matcher' && entry.value.type === 'object') {
            const mm = members(entry.value);
            const ev = mm.get('event')?.value;
            if (ev) idRef(ev, [...p, 'event'], ['event']);
            const tr = mm.get('transition')?.value;
            if (tr) idRef(tr, [...p, 'transition'], ['transition']);
          } else if (type === 'negatives' && entry.value.type === 'array') {
            (entry.value.children ?? []).forEach((neg, i) => {
              if (neg.type !== 'object') return;
              const nm = members(neg);
              const sc = nm.get('scenario')?.value;
              if (sc) idRef(sc, [...p, i, 'scenario'], ['scenario']);
              const fs = nm.get('faults')?.value;
              if (fs) idRefs(fs, [...p, i, 'faults'], ['fault']);
            });
          } else if (type === 'expr' && entry.value.type === 'string') {
            model.exprs.push({ owner: ownerId, path: p, src: entry.value.value, loc: loc(entry.value) });
          }
        }
        return;
      }
      case 'any':
        return;
      default:
        bad('metamodel.type', `${label} has an unsupported meta-model type "${t}".`);
    }
  };

  /**
   * @param {Record<string, any>} fields @param {import('jsonc-parser').Node} node
   * @param {(string|number)[]} path @param {string} ownerId @param {string} label
   */
  const checkFields = (fields, node, path, ownerId, label) => {
    const m = members(node);
    for (const [key, entry] of m) {
      const def = own(fields, key);
      if (!def) { diagnostics.push({ code: 'property.unknown', severity: 'error', message: `Unsupported property "${key}" on ${label}.`, loc: loc(entry.key), path: [...path, key], entityId: ownerId }); continue; }
      if (def.type === 'entities') continue; // handled by caller
      checkValue(def, entry.value, [...path, key], ownerId, `"${key}"`);
    }
    for (const [key, def] of Object.entries(fields)) {
      if (def.required && !m.has(key)) diagnostics.push({ code: 'property.required', severity: 'error', message: `Missing required property "${key}" on ${label}.`, loc: locOf(starts, node.offset, 1), path, entityId: ownerId });
    }
  };

  /**
   * @param {string} kind @param {import('jsonc-parser').Node} node
   * @param {(string|number)[]} path @param {string|null} owner
   */
  const parseEntity = (kind, node, path, owner) => {
    const def = meta.entities[kind];
    if (node.type !== 'object') {
      diagnostics.push({ code: 'entity.type', severity: 'error', message: `A ${def.label.toLowerCase()} must be an object.`, loc: loc(node), path });
      return;
    }
    const m = members(node);
    const idNode = m.get('id')?.value;
    const id = idNode && idNode.type === 'string' ? idNode.value : null;
    if (id === null) {
      diagnostics.push({ code: 'id.missing', severity: 'error', message: `This ${def.label.toLowerCase()} has no string "id".`, loc: locOf(starts, node.offset, 1), path });
      return;
    }
    if (!ID_RE.test(id)) diagnostics.push({ code: 'id.format', severity: 'error', message: `Id "${id}" must be lower-case words joined by hyphens (pattern ${metamodel.idPattern}).`, loc: loc(/** @type {any} */ (idNode)), path: [...path, 'id'], entityId: id });
    const existing = model.entities.get(id);
    if (existing) {
      diagnostics.push({ code: 'id.duplicate', severity: 'error', message: `Id "${id}" is already used by a ${existing.kind} declared on line ${existing.loc.line}.`, loc: loc(/** @type {any} */ (idNode)), path: [...path, 'id'], entityId: id });
      return;
    }
    /** @type {Entity} */
    const entity = { id, kind, data: getNodeValue(node), owner, path, loc: loc(node) };
    model.entities.set(id, entity);
    model.byKind[kind].push(entity);
    checkFields(def.properties, node, path, id, `${kind} "${id}"`);
    for (const [key, pdef] of Object.entries(def.properties)) {
      const p = /** @type {any} */ (pdef);
      if (p.type !== 'entities') continue;
      const entry = m.get(key);
      if (!entry) continue;
      if (entry.value.type !== 'array') { diagnostics.push({ code: 'property.type', severity: 'error', message: `"${key}" must be an array.`, loc: loc(entry.value), path: [...path, key], entityId: id }); continue; }
      (entry.value.children ?? []).forEach((child, i) => parseEntity(p.entity, child, [...path, key, i], id));
    }
  };

  for (const [section, sdef] of Object.entries(meta.sections)) {
    const s = /** @type {any} */ (sdef);
    if (!s.entity) continue;
    const entry = top.get(section);
    if (!entry) {
      if (s.single) diagnostics.push({ code: 'spec.system-missing', severity: 'error', message: 'Missing "system" section.', loc: locOf(starts, root.offset, 1) });
      continue;
    }
    if (s.single) { parseEntity(s.entity, entry.value, [section], null); continue; }
    if (entry.value.type !== 'array') { diagnostics.push({ code: 'spec.section-type', severity: 'error', message: `Section "${section}" must be an array.`, loc: loc(entry.value), path: [section] }); continue; }
    (entry.value.children ?? []).forEach((child, i) => parseEntity(s.entity, child, [section, i], null));
  }
  model.system = model.byKind.system[0] ?? null;

  for (const ref of model.refs) {
    const target = model.entities.get(ref.target);
    if (!target) diagnostics.push({ code: 'ref.unresolved', severity: 'error', message: `"${ref.target}" does not identify any entity (expected ${ref.allowed.includes(ANY_KIND) ? 'any entity' : 'a ' + ref.allowed.join(' or ')}).`, loc: ref.loc, path: ref.path, entityId: ref.from });
    else if (!ref.allowed.includes(ANY_KIND) && !ref.allowed.includes(target.kind)) diagnostics.push({ code: 'ref.kind', severity: 'error', message: `"${ref.target}" is a ${target.kind}; expected a ${ref.allowed.join(' or ')}.`, loc: ref.loc, path: ref.path, entityId: ref.from });
  }

  return { model, diagnostics };
}

/** @param {string} code */
function humanize(code) {
  return code.replace(/([a-z])([A-Z])/g, '$1 $2').toLowerCase();
}

/**
 * JSON.stringify with object keys sorted at every level.
 * @param {any} value @param {number} [indent]
 * @returns {string}
 */
export function stableStringify(value, indent) {
  return JSON.stringify(sortKeys(value), null, indent);
}

/** @param {any} v @returns {any} */
function sortKeys(v) {
  if (Array.isArray(v)) return v.map(sortKeys);
  if (v && typeof v === 'object') {
    /** @type {Record<string, any>} */
    const out = {};
    for (const k of Object.keys(v).sort()) out[k] = sortKeys(v[k]);
    return out;
  }
  return v;
}

/**
 * The normalized semantic content of a model as a plain JSON value.
 * Contains no source locations and no presentation state.
 * @param {Model} model
 */
export function normalize(model) {
  const top = [...model.entities.values()].filter((e) => e.owner === null);
  top.sort((a, b) => (a.id < b.id ? -1 : a.id > b.id ? 1 : 0));
  return sortKeys({
    schemaVersion: model.schemaVersion,
    vocabulary: model.vocabulary ?? {},
    entities: top.map((e) => ({ kind: e.kind, ...e.data })),
  });
}

/**
 * 53-bit string hash (cyrb53), rendered as 14 hex digits. Not cryptographic;
 * used for revision identity and change detection.
 * @param {string} str
 */
export function hashString(str) {
  let h1 = 0xdeadbeef, h2 = 0x41c6ce57;
  for (let i = 0; i < str.length; i++) {
    const ch = str.charCodeAt(i);
    h1 = Math.imul(h1 ^ ch, 2654435761);
    h2 = Math.imul(h2 ^ ch, 1597334677);
  }
  h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507) ^ Math.imul(h2 ^ (h2 >>> 13), 3266489909);
  h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507) ^ Math.imul(h1 ^ (h1 >>> 13), 3266489909);
  return (4294967296 * (2097151 & h2) + (h1 >>> 0)).toString(16).padStart(14, '0');
}

/**
 * Hash of the normalized semantic content.
 * @param {Model|null} model
 */
export function semanticHash(model) {
  return model ? hashString(JSON.stringify(normalize(model))) : '00000000000000';
}
