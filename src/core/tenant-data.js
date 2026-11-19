// The rules of a metadata model (WG-4950): in a system whose tenants describe their own data, the database model is
// data too. Platform records are fixed tables; tenant domain data is described only by the tenant-schema metamodel
// (types with a `metamodel` role) and stored in platform tables of scope tenant-meta, never as a fixed record type of
// its own. Errors, always on. Pure and deterministic.
//
//   record.tenant-data-fixed  a record that names a tenant object or carries tenant field values is tenant-meta
//   record.scope-missing      once a type has metamodel tenant-schema, every record states its scope
//   record.described-by       a tenant-meta record names the tenant-schema type that describes it, and only it does

import { parseTypeName } from './codegen-model.js';
import { recordFields } from './data-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** The metamodel roles a type may have. */
export const METAMODEL_ROLES = Object.freeze(['tenant-schema', 'object-id', 'field-id', 'values', 'definition']);

/**
 * The metamodel role of a declared type, or undefined.
 * @param {Model} model @param {string} name
 * @returns {string|undefined}
 */
function roleOf(model, name) {
  const t = model.entities.get(name);
  return t?.kind === 'type' && typeof t.data.metamodel === 'string' ? t.data.metamodel : undefined;
}

/**
 * Why a record field's type carries tenant domain data, or undefined: a type (through list and option) whose role is
 * object-id (the field names a tenant object) or values (the field holds a tenant record's field values), or a map
 * keyed by a field-id type (a generic map of field values).
 * @param {Model} model @param {any} type
 * @returns {string|undefined}
 */
export function tenantDataReason(model, type) {
  if (typeof type !== 'string') return undefined;
  const p = parseTypeName(type);
  if (p.k === 'list' || p.k === 'option' || p.k === 'set' || p.k === 'shared') return tenantDataReason(model, p.of);
  if (p.k === 'map') {
    if (roleOf(model, p.key) === 'field-id') return `is a map keyed by the tenant field id "${p.key}"`;
    return tenantDataReason(model, p.value);
  }
  const role = roleOf(model, p.name);
  if (role === 'object-id') return `names a tenant object type ("${p.name}")`;
  if (role === 'values') return `holds a tenant record's field values ("${p.name}")`;
  return undefined;
}

/**
 * The consistency rules of the metadata model.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkTenantData(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });

  const schemaTypes = (model.byKind.type ?? []).filter((t) => t.data.metamodel === 'tenant-schema');
  for (const r of model.byKind.record ?? []) {
    const scope = r.data.scope;
    if (scope === undefined && schemaTypes.length) {
      err('record.scope-missing', r, `Record "${r.id}" states no "scope". Tenants describe their own data here (type "${schemaTypes[0].id}" is the tenant schema), so every record says whether it is a platform table ("platform") or a platform table carrying tenant-defined data ("tenant-meta").`, ['id']);
    }
    if (scope !== 'tenant-meta') {
      for (const { field, index } of recordFields(r)) {
        const why = tenantDataReason(model, field.type);
        if (why === undefined) continue;
        err('record.tenant-data-fixed', r, `Record "${r.id}" is a fixed record type for tenant domain data: its field "${field.name}" ${why}. Tenant data is described only by the tenant schema; store it in a platform table of scope "tenant-meta" (a generic record) instead.`, ['fields', index, 'type']);
        break;
      }
    }
    const by = r.data.describedBy;
    if (scope === 'tenant-meta') {
      const target = typeof by === 'string' ? model.entities.get(by) : undefined;
      if (by === undefined) err('record.described-by', r, `Record "${r.id}" has scope "tenant-meta" and needs "describedBy": the type with metamodel "tenant-schema" that describes its rows.`, ['scope']);
      else if (target?.kind === 'type' && target.data.metamodel !== 'tenant-schema') err('record.described-by', r, `Record "${r.id}" is described by "${by}", which is not a type with metamodel "tenant-schema".`, ['describedBy']);
    } else if (by !== undefined) {
      err('record.described-by', r, `Record "${r.id}" has "describedBy" but its scope is ${scope === undefined ? 'not stated' : `"${scope}"`}; only a "tenant-meta" record is described by the tenant schema.`, ['describedBy']);
    }
  }
  return out;
}
