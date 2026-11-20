// The typed sections of a product file: each value is checked against a platform type (WG-5046).
//
// A product file declares tenant metadata that has no entity kind of its own in the specification
// format: object types, policies, segments, settings, ledger units, pools and limits, mail and notice
// templates, tokens, triggers, automations and operations (D-6580). Their shape is a type of the
// platform specification, the one the tenant bundle carries (bundle-sections). One table,
// TYPED_SECTIONS, maps each section to that type, and one check, checkTypedItem, tests a value
// against a declared type: the fields of a struct (required and optional), the variants of a union by
// tag, the values of an enum, lists, maps, ids by pattern and length, and scalars by representation.
// specc applies the same table and the same check (crates/spec-compiler/src/layer_values.rs there),
// and both give the same rule codes:
//
//   layer.value-invalid       a value that does not have the shape of its platform type
//   layer.outside-catalogue   a union value whose variant the platform's union lacks (the published
//                             catalogue of INT-153: a trigger event, an automation step, an operation step)
//
// The names a value holds that refer to an entity of the product (an object type, a ledger unit, a
// template, a role, an automation) are returned as references for layers.js to resolve once every
// product file is read (layer.reference-unknown, layer.cross-product-reference).
//
// Expressions are written in the authoring syntax of the tenant rule language, as text, wherever the
// platform type is the AST `expr` or the text type `expression` (AUTHORING_TEXT_TYPES). The check here collects
// each such text with its path (`exprs`); layer-expr.js parses and checks it against the scope it is in (WG-5060).

import { parseTypeName } from './codegen-model.js';

/**
 * One typed section: the platform type each value conforms to, and the member of the value that names
 * it (`idField`; the item's `id` is taken for it when the item leaves it out, and refused when it
 * differs). `idField: null`: the type has no name, and the item's `id` is only the product's name for it.
 * @typedef {{section: string, type: string, idField: string|null, purpose: string}} TypedSection
 */

/** The typed sections, in the order the messages list them (D-6580). @type {readonly TypedSection[]} */
export const TYPED_SECTIONS = Object.freeze([
  { section: 'objects', type: 'object-type-def', idField: 'id', purpose: 'object types (values of the platform type object-type-def)' },
  { section: 'policies', type: 'policy-def', idField: 'id', purpose: 'policies of roles over object types (policy-def)' },
  { section: 'queries', type: 'query-def', idField: 'id', purpose: 'named queries over object types (values of the platform type query-def)' },
  { section: 'views', type: 'view-def', idField: 'id', purpose: 'views that present queries at a route (values of the platform type view-def)' },
  { section: 'workflows', type: 'workflow-def', idField: 'id', purpose: 'workflows of a field of an object type: its states and the transitions between them (values of the platform type workflow-def)' },
  { section: 'segments', type: 'segment-decl', idField: null, purpose: 'segments (segment-decl)' },
  { section: 'settings', type: 'setting-def', idField: 'id', purpose: 'setting definitions (setting-def)' },
  { section: 'ledgerUnits', type: 'ledger-unit-decl', idField: 'unit', purpose: 'ledger units (ledger-unit-decl)' },
  { section: 'ledgerPools', type: 'ledger-pool-decl', idField: 'pool', purpose: 'ledger pools (ledger-pool-decl)' },
  { section: 'ledgerLimits', type: 'ledger-limit', idField: null, purpose: 'floors, caps and period caps of ledger accounts (ledger-limit)' },
  { section: 'mailTemplates', type: 'mail-template-decl', idField: 'template', purpose: 'mail templates (mail-template-decl)' },
  { section: 'noticeTemplates', type: 'notice-template-decl', idField: 'template', purpose: 'notice templates (notice-template-decl)' },
  { section: 'tokens', type: 'token-decl', idField: 'name', purpose: 'tokens of templates (token-decl)' },
  { section: 'triggers', type: 'trigger-def', idField: 'id', purpose: 'triggers (values of the platform type trigger-def)' },
  { section: 'automations', type: 'automation-def', idField: 'id', purpose: 'automations (values of the platform type automation-def)' },
  { section: 'operations', type: 'tenant-operation-def', idField: 'id', purpose: 'composite operations (values of the platform type tenant-operation-def)' },
]);

/** The typed section called `section`. @param {string} section */
export const typedSection = (section) => TYPED_SECTIONS.find((s) => s.section === section);

/**
 * Platform id types whose value, in a product file, names an entity of the product, with the sections
 * it is declared in. A value in the product's own namespace must be declared there; one without a
 * namespace names something outside the product and is not checked. These types are checked by their
 * pattern and length only: segment-id is a uuid once installed (D-6582), and a product names its
 * segment by its namespaced key.
 * @type {Readonly<Record<string, readonly string[]>>}
 */
export const REFERENCE_TYPES = Object.freeze({
  'object-type-id': ['objects'],
  'ledger-unit': ['ledgerUnits'],
  'ledger-pool-name': ['ledgerPools'],
  'role-id': ['roles'],
  'policy-id': ['policies'],
  'workflow-id': ['automations', 'workflows'],
  'query-id': ['queries'],
  'view-id': ['views'],
  'template-id': ['mailTemplates', 'noticeTemplates'],
  'setting-id': ['settings'],
  'segment-id': ['segments'],
});

/** Platform types whose value may be written as text in the authoring syntax of the tenant rule language instead of as the AST (D-6546). */
export const AUTHORING_TEXT_TYPES = Object.freeze(['expr', 'expression']);

/** The separator between the namespace of a product and the local name (D-6582). */
export const NAMESPACE_SEPARATOR = '__';

/**
 * The namespace of the entities of a product: its id with each hyphen replaced by an underscore,
 * followed by two underscores (D-6582).
 * @param {string} productId
 */
export const namespaceOf = (productId) => `${productId.replaceAll('-', '_')}${NAMESPACE_SEPARATOR}`;

/** @param {string} text */
const isUuid = (text) => /^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$/.test(text);

/** @param {string} text @param {string} case_ How a variant name is written as the tag of a value, under the union's variantCase. */
function variantTag(text, case_) {
  if (case_ === 'PascalCase') return text.split(/[-_]/).map((w) => w.charAt(0).toUpperCase() + w.slice(1)).join('');
  if (case_ === 'snake_case') return text.replaceAll('-', '_');
  return text;
}

/** @param {(string|number)[]} path */
const place = (path) => (path.length === 0 ? 'its value' : `"${path.join('.')}"`);

/**
 * @typedef {{code: string, path: (string|number)[], message: string}} Problem
 * @typedef {{path: (string|number)[], name: string, sections: readonly string[]}} Ref
 * @typedef {{path: (string|number)[], text: string}} ExprText   an expression written as text, and where
 */

/**
 * Check one item of a typed section against its platform type.
 *
 * @param {(name: string) => any} types the declaration of a platform type, or undefined
 * @param {string} file the product file
 * @param {TypedSection} section
 * @param {string} id the item's id
 * @param {any} item the item as a plain value
 * @returns {{problems: Problem[], refs: Ref[], exprs: ExprText[]}}
 */
export function checkTypedItem(types, file, section, id, item) {
  /** @type {Problem[]} */
  const problems = [];
  /** @type {Ref[]} */
  const refs = [];
  /** @type {ExprText[]} */
  const exprs = [];
  if (item === null || typeof item !== 'object' || Array.isArray(item)) return { problems, refs, exprs };
  const bad = (/** @type {(string|number)[]} */ path, /** @type {string} */ problem) => {
    problems.push({ code: 'layer.value-invalid', path, message: `"${id}" in ${file}: ${place(path)} ${problem}. A value in this section has the platform type "${section.type}"; correct it to match that type in the platform specification.` });
  };
  const value = { ...item };
  if (section.idField !== 'id') delete value.id;
  if (section.idField && section.idField !== 'id') {
    if (value[section.idField] === undefined) value[section.idField] = id;
    else if (value[section.idField] !== id) bad([section.idField], `is ${JSON.stringify(value[section.idField])}, but must be the id "${id}" of the item, or be left out`);
  }
  const root = types(section.type);
  if (!root) {
    bad([], `cannot be checked: the platform specification declares no type "${section.type}"`);
    return { problems, refs, exprs };
  }

  /** @param {string} ty @param {any} v @param {(string|number)[]} path */
  const check = (ty, v, path) => {
    const p = parseTypeName(ty);
    switch (p.k) {
      case 'option': if (v !== null && v !== undefined) check(p.of, v, path); return;
      case 'shared': check(p.of, v, path); return;
      case 'list': case 'set':
        if (!Array.isArray(v)) bad(path, `must be a list of ${p.of}`);
        else v.forEach((x, i) => check(p.of, x, [...path, i]));
        return;
      case 'map':
        if (v === null || typeof v !== 'object' || Array.isArray(v)) { bad(path, `must be a map from ${p.key} to ${p.value}`); return; }
        for (const [k, x] of Object.entries(v)) {
          const at = [...path, k];
          check(p.key, k, at);
          check(p.value, x, at);
          if (x && typeof x === 'object' && typeof x.id === 'string' && x.id !== k) bad(at, `is keyed "${k}" but names itself "${x.id}"`);
        }
        return;
      default: named(p.name, v, path);
    }
  };

  /** @param {string} name @param {any} v @param {(string|number)[]} path */
  const named = (name, v, path) => {
    switch (name) {
      case 'string': case 'uuid': case 'bytes':
        if (typeof v !== 'string') bad(path, `must be a string (${name})`);
        else if (name === 'uuid' && !isUuid(v)) bad(path, `must be a uuid, not "${v}"`);
        return;
      case 'bool': if (typeof v !== 'boolean') bad(path, 'must be true or false'); return;
      case 'u8': case 'u16': case 'u32': case 'u64':
        if (!Number.isInteger(v) || v < 0) bad(path, `must be a non-negative whole number (${name})`);
        return;
      case 'i32': case 'i64': case 'timestamp': case 'duration':
        if (!Number.isInteger(v)) bad(path, `must be a whole number (${name})`);
        return;
      case 'f64': if (typeof v !== 'number') bad(path, 'must be a number'); return;
      case 'json': return;
      default: {
        const t = types(name);
        if (!t) bad(path, `names the type "${name}", which the platform specification does not declare`);
        else declared(name, t, v, path, null);
      }
    }
  };

  /** @param {string} name @param {any} t @param {any} v @param {(string|number)[]} path @param {string|null} declField */
  const declared = (name, t, v, path, declField) => {
    if (AUTHORING_TEXT_TYPES.includes(name) && typeof v === 'string') { exprs.push({ path, text: v }); return; }
    switch (t.kind) {
      case 'struct': strukt(t.fields ?? [], v, path, declField); return;
      case 'enum':
        if (!(typeof v === 'string' && (t.values ?? []).includes(v))) bad(path, `must be one of ${(t.values ?? []).join(', ')} (${name})`);
        return;
      case 'union': union(name, t, v, path); return;
      default: scalar(name, t, v, path);
    }
  };

  /** An `id` or `scalar` type: its representation, pattern and length. @param {string} name @param {any} t @param {any} v @param {(string|number)[]} path */
  const scalar = (name, t, v, path) => {
    const reference = Object.hasOwn(REFERENCE_TYPES, name) ? REFERENCE_TYPES[name] : null;
    const before = problems.length;
    if (reference) { if (typeof v !== 'string') bad(path, `must be the name of an entity (${name}), written as a string`); }
    else check(t.repr ?? 'string', v, path);
    if (problems.length > before || typeof v !== 'string') return;
    const c = t.constraints;
    if (c?.maxLength !== undefined && [...v].length > c.maxLength) { bad(path, `is longer than ${c.maxLength} characters (${name})`); return; }
    if (c?.pattern !== undefined && !new RegExp(c.pattern).test(v)) { bad(path, `is "${v}", which does not match the pattern ${c.pattern} of ${name}`); return; }
    if (reference) refs.push({ path, name: v, sections: reference });
  };

  /** @param {any[]} fields @param {any} v @param {(string|number)[]} path @param {string|null} declField */
  const strukt = (fields, v, path, declField) => {
    if (v === null || typeof v !== 'object' || Array.isArray(v)) { bad(path, 'must be an object'); return; }
    const names = fields.map((f) => f.name);
    for (const k of Object.keys(v)) if (!names.includes(k)) bad([...path, k], `is not a field of its type; the fields are ${names.join(', ')}`);
    for (const f of fields) {
      const ty = f.type ?? 'json';
      const optional = f.optional === true || parseTypeName(ty).k === 'option';
      if (v[f.name] === undefined) {
        if (!optional) bad(path, `lacks the required field "${f.name}" (${ty})`);
        continue;
      }
      if (declField === f.name) {
        // The member that names the item is a declaration, not a reference.
        const before = refs.length;
        check(ty, v[f.name], [...path, f.name]);
        refs.length = before;
      } else check(ty, v[f.name], [...path, f.name]);
    }
  };

  /** @param {string} name @param {any} t @param {any} v @param {(string|number)[]} path */
  const union = (name, t, v, path) => {
    const internal = t.encoding?.tag === 'internal';
    const tagField = t.encoding?.tagField ?? 'type';
    const case_ = t.encoding?.variantCase ?? '';
    /** @type {any[]} */
    const variants = t.variants ?? [];
    const tagOf = (/** @type {any} */ x) => variantTag(x.name ?? '', case_);
    const listing = variants.map(tagOf).join(', ');
    const written = internal ? `{"${tagField}": "<Variant>", ... }` : '{"<Variant>": { ... }}, or "<Variant>" for a variant without fields';
    const shape = () => bad(path, `must be one variant of the union "${name}", written ${written}; the variants are ${listing}`);
    /** @type {string} */
    let tag;
    /** @type {any} */
    let payload;
    if (typeof v === 'string' && !internal) { tag = v; payload = undefined; }
    else if (v !== null && typeof v === 'object' && !Array.isArray(v) && internal) {
      if (typeof v[tagField] !== 'string') { shape(); return; }
      tag = v[tagField];
      const { [tagField]: _tag, ...rest } = v;
      payload = rest;
    } else if (v !== null && typeof v === 'object' && !Array.isArray(v) && Object.keys(v).length === 1) {
      tag = Object.keys(v)[0];
      payload = v[tag];
    } else { shape(); return; }
    const variant = variants.find((x) => tagOf(x) === tag);
    if (!variant) {
      problems.push({ code: 'layer.outside-catalogue', path, message: `"${id}" in ${file} names "${tag}" at ${path.length === 0 ? 'its value' : path.join('.')}, which is outside the published catalogue (INT-153): the platform's union "${name}" has the variants ${listing}. Use one of them; a kind the catalogue lacks belongs in the platform specification, not in a product.` });
      return;
    }
    /** @type {any[]} */
    const fields = variant.fields ?? [];
    const at = [...path, tag];
    if (variant.newtype === true) {
      const inner = fields[0]?.type ?? 'json';
      if (payload === undefined) bad(at, `needs a value of type ${inner}`); else check(inner, payload, at);
    } else if (variant.tuple !== undefined) {
      if (!Array.isArray(payload)) bad(at, 'must be a list');
    } else if (fields.length === 0) {
      if (payload !== undefined && payload !== null && !(typeof payload === 'object' && Object.keys(payload).length === 0)) bad(at, `takes no fields: write "${tag}" alone`);
    } else if (payload === undefined) {
      const required = fields.filter((f) => f.optional !== true && parseTypeName(f.type ?? 'json').k !== 'option').map((f) => f.name);
      if (required.length) bad(path, `names "${tag}" without its fields ${required.join(', ')}`);
    } else strukt(fields, payload, at, null);
  };

  declared(section.type, root, value, [], section.idField);
  return { problems, refs, exprs };
}
