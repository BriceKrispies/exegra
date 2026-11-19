// The data model: records (owning component, key, fields with personal class,
// references and roles) and copies of them (held by a component, with a scope,
// a freshness bound and an erasure point). The kinds are declared in
// metamodel.json and checked structurally by the parser; this module holds the
// rules that need the whole model:
//
//   consistency (errors)   a record's key and a copy's fields name declared fields,
//                          a numeric bound has a unit
//   data rules (warnings)  the six computed rules below, each finding naming the
//                          entity and the field
//
// The same findings drive validation (validate.js), the data-model claim method
// (claims.js), the Data projection and the inspector. Pure and deterministic.

import { componentGraph, ancestorsOf } from './query.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** The literal a field's refersTo uses for a principal id. */
export const PRINCIPAL = 'principal';

export const DATA_RULES = /** @type {const} */ ({
  'erasure-point': { label: 'Erasure point', doc: 'Every copy that holds a personal field or a principal reference states an erasure point (PER-109).' },
  'record-erasure-point': { label: 'Record erasure point', doc: 'Every record with a personal field (or a credential field) states an erasure point or a bounded retention (erasure.point, or erasure.bound with a unit), or has a retention construct that deletes it or anonymises every such field.' },
  'no-principal-in-shared': { label: 'No principal data in a shared copy', doc: 'No shared copy holds a field that refers to the principal or is personal, or depends on authority (D-136).' },
  'party-by-id': { label: 'Party fields by principal id', doc: 'Every field with role party refers to the principal and has a type that is not a name (D-137).' },
  'freshness-bound': { label: 'Freshness bound', doc: 'Every copy states a freshness bound.' },
  'holder-reaches-owner': { label: 'Holder related to owner', doc: "A copy's holder is the owner of each record it copies, contains it or is contained in it, or a directed relationship path leads from one to the other." },
});
/** @typedef {keyof typeof DATA_RULES} DataRule */
export const RULE_IDS = /** @type {DataRule[]} */ (Object.keys(DATA_RULES));

/**
 * @typedef {Object} Finding
 * @property {DataRule} rule
 * @property {string} entityId      the copy or record the finding is about
 * @property {string[]} fields      the fields concerned, as record.field (empty when the finding is about the copy as a whole)
 * @property {string[]} records     records involved
 * @property {(string|number)[]} sub  path below the entity
 * @property {string} message
 */

/**
 * @typedef {Object} HeldField
 * @property {Entity} record
 * @property {any} field   the field declaration
 * @property {number} index index in the record's fields
 * @property {number|null} at index in the copy's fields list, null when the copy holds every field
 */

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/** The well-formed field declarations of a record, with their index. @param {Entity} record */
export function recordFields(record) {
  const list = Array.isArray(record.data.fields) ? record.data.fields : [];
  return list.map((/** @type {any} */ f, /** @type {number} */ index) => ({ field: f, index })).filter(({ field }) => isObj(field) && typeof field.name === 'string');
}

/** The records a copy is of, resolved. @param {Model} model @param {Entity} copy @returns {Entity[]} */
export function sourcesOf(model, copy) {
  const ids = Array.isArray(copy.data.of) ? copy.data.of : [];
  /** @type {Entity[]} */
  const out = [];
  for (const id of ids) {
    const e = typeof id === 'string' ? model.entities.get(id) : undefined;
    if (e && e.kind === 'record' && !out.includes(e)) out.push(e);
  }
  return out;
}

/** Copies whose `of` names the record. @param {Model} model @param {string} recordId @returns {Entity[]} */
export function copiesOf(model, recordId) {
  return (model.byKind.copy ?? []).filter((c) => Array.isArray(c.data.of) && c.data.of.includes(recordId));
}

/**
 * The fields a copy holds, resolved against its source records. A name is a
 * field of exactly one source record, or record-id.field.
 * @param {Model} model @param {Entity} copy
 * @returns {{held: HeldField[], unknown: {name: string, at: number}[], ambiguous: {name: string, at: number, records: string[]}[]}}
 */
export function copyFields(model, copy) {
  const sources = sourcesOf(model, copy);
  /** @type {HeldField[]} */
  const held = [];
  /** @type {{name: string, at: number}[]} */
  const unknown = [];
  /** @type {{name: string, at: number, records: string[]}[]} */
  const ambiguous = [];
  if (!Array.isArray(copy.data.fields)) {
    for (const record of sources) for (const { field, index } of recordFields(record)) held.push({ record, field, index, at: null });
    return { held, unknown, ambiguous };
  }
  copy.data.fields.forEach((/** @type {any} */ name, /** @type {number} */ at) => {
    if (typeof name !== 'string') return;
    const dot = name.indexOf('.');
    /** @type {HeldField[]} */
    let matches = [];
    if (dot > 0) {
      const record = sources.find((r) => r.id === name.slice(0, dot));
      const fname = name.slice(dot + 1);
      if (record) matches = recordFields(record).filter(({ field }) => field.name === fname).map(({ field, index }) => ({ record, field, index, at }));
    } else {
      for (const record of sources) for (const { field, index } of recordFields(record)) if (field.name === name) matches.push({ record, field, index, at });
    }
    if (!matches.length) unknown.push({ name, at });
    else if (matches.length > 1) ambiguous.push({ name, at, records: matches.map((m) => m.record.id) });
    else held.push(matches[0]);
  });
  return { held, unknown, ambiguous };
}

/** A field names or identifies a principal: personal data, or a principal id. @param {any} f */
export const isPrincipalData = (f) => typeof f.personal === 'string' || f.refersTo === PRINCIPAL;

/**
 * A field whose record must state how it is erased: personal data (a personal
 * class), or a credential. A credential is treated like personal data for this
 * rule only, because keeping one past the end of its owner is the worse error.
 * @param {any} f
 */
export const isErasableRecordField = (f) => typeof f.personal === 'string' || f.classification === 'personal' || f.classification === 'credential';

/** A record states an erasure point or a bounded retention. @param {any} erasure */
export const erasureStated = (erasure) => isObj(erasure) && (
  (typeof erasure.point === 'string' && erasure.point.trim() !== '') ||
  (typeof erasure.bound === 'number' && Number.isFinite(erasure.bound) && typeof erasure.unit === 'string')
);

/**
 * A retention construct of the record (section retentions) that removes its erasable fields when it ends:
 * delete, or anonymise naming every one of them. Its keepFor or until is the erasure point.
 * @param {Model} model @param {Entity} record @param {string[]} names
 */
const retentionErases = (model, record, names) => (model.byKind.retention ?? []).some((t) => t.data.record === record.id && (
  t.data.then === 'delete' || (t.data.then === 'anonymise' && Array.isArray(t.data.fields) && names.every((n) => t.data.fields.includes(n)))));

/** A type that is a name rather than an id: its text contains the word name or handle. @param {any} type */
export const isNameType = (type) => typeof type === 'string' && /(^|[^a-z])(name|handle)s?($|[^a-z])/i.test(type);

/** @param {HeldField} h */
const qualified = (h) => `${h.record.id}.${h.field.name}`;

/** @param {any} bound */
const hasBound = (bound) => (typeof bound === 'number' && Number.isFinite(bound)) || (typeof bound === 'string' && bound.trim() !== '');

/**
 * Consistency checks of records and copies (errors).
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkDataConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} sub */
  const err = (code, e, message, sub) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  for (const r of model.byKind.record ?? []) {
    const seen = new Set();
    for (const { field, index } of recordFields(r)) {
      if (seen.has(field.name)) err('record.field-duplicate', r, `Record "${r.id}" declares field "${field.name}" twice.`, ['fields', index, 'name']);
      seen.add(field.name);
    }
    (Array.isArray(r.data.key) ? r.data.key : []).forEach((/** @type {any} */ k, /** @type {number} */ i) => {
      if (typeof k === 'string' && !seen.has(k)) err('record.key-field', r, `Key "${k}" of record "${r.id}" is not one of its fields.`, ['key', i]);
    });
    // One way to say personal: the personal class. A classification of personal must
    // go with a class, and a field with a class may only be classified personal.
    for (const { field, index } of recordFields(r)) {
      if (field.classification === 'personal' && typeof field.personal !== 'string') err('field.classification-personal', r, `Field "${field.name}" of record "${r.id}" is classified personal but names no personal-data class; give its class in "personal".`, ['fields', index, 'classification']);
      if (typeof field.personal === 'string' && field.classification !== undefined && field.classification !== 'personal') err('field.classification-conflict', r, `Field "${field.name}" of record "${r.id}" has personal class "${field.personal}" and classification "${field.classification}"; a personal field is classified personal or not at all.`, ['fields', index, 'classification']);
    }
    const erasure = r.data.erasure;
    if (isObj(erasure) && typeof erasure.bound === 'number' && erasure.unit === undefined) err('record.bound-unit', r, `The erasure bound of record "${r.id}" is a number and needs a "unit".`, ['erasure', 'bound']);
  }
  for (const c of model.byKind.copy ?? []) {
    const of = Array.isArray(c.data.of) ? c.data.of : [];
    if (!of.length) err('copy.of-empty', c, `Copy "${c.id}" must name at least one record in "of".`, ['of']);
    const { unknown, ambiguous } = copyFields(model, c);
    for (const u of unknown) err('copy.field-unknown', c, `Copy "${c.id}" holds "${u.name}", which is not a field of ${of.length === 1 ? `record "${of[0]}"` : `any of ${of.map((/** @type {any} */ x) => `"${x}"`).join(', ')}`}.`, ['fields', u.at]);
    for (const a of ambiguous) err('copy.field-ambiguous', c, `Field "${a.name}" of copy "${c.id}" is declared by ${a.records.join(' and ')}; write record-id.${a.name}.`, ['fields', a.at]);
    for (const part of ['freshness', 'erasure']) {
      const v = c.data[part];
      if (!isObj(v)) continue;
      if (typeof v.bound === 'number' && v.unit === undefined) err('copy.bound-unit', c, `The ${part} bound of copy "${c.id}" is a number and needs a "unit".`, [part, 'bound']);
      if (part === 'freshness' && v.bound !== undefined && typeof v.bound !== 'number' && typeof v.bound !== 'string') err('copy.freshness-bound', c, `The freshness bound of copy "${c.id}" must be a number or a text.`, [part, 'bound']);
    }
  }
  return out;
}

/**
 * Compute the six data rules.
 * @param {Model} model
 * @returns {{findings: Finding[], checked: Record<DataRule, number>}}
 *   `checked` counts, per rule, what the rule looked at: copies with principal data,
 *   shared copies, party fields, copies, and (copy, record) pairs.
 */
export function dataFindings(model) {
  /** @type {Finding[]} */
  const findings = [];
  /** @type {Record<DataRule, number>} */
  const checked = { 'erasure-point': 0, 'record-erasure-point': 0, 'no-principal-in-shared': 0, 'party-by-id': 0, 'freshness-bound': 0, 'holder-reaches-owner': 0 };
  const copies = model.byKind.copy ?? [];
  if (!copies.length && !(model.byKind.record ?? []).length) return { findings, checked };
  const graph = componentGraph(model);

  for (const c of copies) {
    const { held } = copyFields(model, c);
    const records = sourcesOf(model, c).map((r) => r.id);
    const principalData = held.filter((h) => isPrincipalData(h.field));
    /** @param {HeldField[]} hs */
    const fieldSub = (hs) => (hs[0] && hs[0].at !== null ? ['fields', hs[0].at] : ['of']);

    // 1. Erasure point.
    if (principalData.length) {
      checked['erasure-point']++;
      const point = isObj(c.data.erasure) ? c.data.erasure.point : undefined;
      if (!(typeof point === 'string' && point.trim())) {
        findings.push({
          rule: 'erasure-point', entityId: c.id, fields: principalData.map(qualified), records, sub: ['erasure'],
          message: `Copy "${c.id}" holds ${describe(principalData)} but states no erasure point, so a deletion cannot be shown to reach it.`,
        });
      }
    }

    // 2. No principal data in a shared copy (D-136).
    if (c.data.scope === 'shared') {
      checked['no-principal-in-shared']++;
      if (principalData.length) {
        findings.push({
          rule: 'no-principal-in-shared', entityId: c.id, fields: principalData.map(qualified), records, sub: fieldSub(principalData),
          message: `Shared copy "${c.id}" holds ${describe(principalData)}; a copy served to more than one viewer must not name a principal.`,
        });
      }
      if (c.data.dependsOnAuthority === true) {
        findings.push({
          rule: 'no-principal-in-shared', entityId: c.id, fields: [], records, sub: ['dependsOnAuthority'],
          message: `Shared copy "${c.id}" depends on authority; a copy served to more than one viewer cannot depend on who is asking.`,
        });
      }
    }

    // 4. Freshness bound.
    checked['freshness-bound']++;
    if (!(isObj(c.data.freshness) && hasBound(c.data.freshness.bound))) {
      findings.push({ rule: 'freshness-bound', entityId: c.id, fields: [], records, sub: ['freshness'], message: `Copy "${c.id}" states no freshness bound.` });
    }

    // 5. The holder is related to each record's owner.
    const holder = typeof c.data.heldBy === 'string' ? model.entities.get(c.data.heldBy) : undefined;
    if (holder && holder.kind === 'component') {
      for (const r of sourcesOf(model, c)) {
        const owner = typeof r.data.owner === 'string' ? model.entities.get(r.data.owner) : undefined;
        if (!owner || owner.kind !== 'component') continue;
        checked['holder-reaches-owner']++;
        if (related(model, graph, holder.id, owner.id)) continue;
        findings.push({
          rule: 'holder-reaches-owner', entityId: c.id, fields: [], records: [r.id], sub: ['heldBy'],
          message: `Copy "${c.id}" is held by "${holder.id}", but no relationship path leads between it and "${owner.id}", the owner of record "${r.id}", in either direction.`,
        });
      }
    }
  }

  // 6. Record erasure point: a record with a personal (or credential) field states how it is erased.
  for (const r of model.byKind.record ?? []) {
    const erasable = recordFields(r).filter(({ field }) => isErasableRecordField(field));
    if (!erasable.length) continue;
    checked['record-erasure-point']++;
    if (erasureStated(r.data.erasure) || retentionErases(model, r, erasable.map(({ field }) => field.name))) continue;
    const fields = erasable.map(({ field }) => `${r.id}.${field.name}`);
    findings.push({
      rule: 'record-erasure-point', entityId: r.id, fields, records: [r.id], sub: ['erasure'],
      message: `Record "${r.id}" holds ${describeRecord(erasable.map(({ field }) => field))} but states neither an erasure point nor a bounded retention, so a deletion cannot be shown to remove it.`,
    });
  }

  // 3. Party fields by principal id (D-137).
  for (const r of model.byKind.record ?? []) {
    for (const { field, index } of recordFields(r)) {
      if (field.role !== 'party') continue;
      checked['party-by-id']++;
      const problems = [];
      if (field.refersTo !== PRINCIPAL) problems.push(field.refersTo === undefined ? 'does not refer to the principal' : `refers to "${field.refersTo}", not the principal`);
      if (isNameType(field.type)) problems.push(`has the name type "${field.type}"`);
      if (problems.length) {
        findings.push({
          rule: 'party-by-id', entityId: r.id, fields: [`${r.id}.${field.name}`], records: [r.id], sub: ['fields', index],
          message: `Party field "${field.name}" of record "${r.id}" ${problems.join(' and ')}; a party is held by principal id, never by name.`,
        });
      }
    }
  }
  return { findings, checked };
}

/** @param {any[]} fs */
function describeRecord(fs) {
  const parts = fs.map((f) => `"${f.name}" (${typeof f.personal === 'string' ? `personal: ${f.personal}` : f.classification})`);
  return `${parts.length === 1 ? 'field' : 'fields'} ${parts.join(', ')}`;
}

/** @param {HeldField[]} hs */
function describe(hs) {
  const parts = hs.map((h) => `${qualified(h)} (${typeof h.field.personal === 'string' ? `personal: ${h.field.personal}` : 'principal id'})`);
  return `${parts.length === 1 ? 'field' : 'fields'} ${parts.join(', ')}`;
}

/**
 * Same component, containment either way, or a directed path either way.
 * @param {Model} model @param {Map<string, {to: string}[]>} graph @param {string} a @param {string} b
 */
function related(model, graph, a, b) {
  if (a === b) return true;
  if (ancestorsOf(model, a).includes(b) || ancestorsOf(model, b).includes(a)) return true;
  return reaches(graph, a, b) || reaches(graph, b, a);
}

/** @param {Map<string, {to: string}[]>} graph @param {string} from @param {string} to */
function reaches(graph, from, to) {
  const seen = new Set([from]);
  const queue = [from];
  for (let i = 0; i < queue.length; i++) {
    for (const e of graph.get(queue[i]) ?? []) {
      if (e.to === to) return true;
      if (!seen.has(e.to)) { seen.add(e.to); queue.push(e.to); }
    }
  }
  return false;
}

/**
 * The data rules as validation warnings, code data.<rule>.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function dataRuleDiagnostics(model) {
  return dataFindings(model).findings.map((f) => {
    const e = /** @type {Entity} */ (model.entities.get(f.entityId));
    return { code: `data.${f.rule}`, severity: /** @type {const} */ ('warning'), message: f.message, entityId: e.id, loc: e.loc, path: [...e.path, ...f.sub] };
  });
}

/**
 * Evaluate a data-model claim: `rules` (default: all six), optionally narrowed
 * to the copies and fields of `records`.
 * @param {Model} model @param {any} ev
 * @returns {{status: 'verified'|'violated'|'inconclusive', scope: string, explanation: string, selected: string[], counterexample?: {summary: string, entities: string[]}}}
 */
export function evaluateDataClaim(model, ev) {
  const rules = Array.isArray(ev.rules) ? ev.rules : RULE_IDS;
  const unknown = rules.filter((/** @type {any} */ r) => !RULE_IDS.includes(r));
  if (unknown.length) return { status: 'inconclusive', scope: 'Nothing was checked.', explanation: `Unknown data rule${unknown.length === 1 ? '' : 's'} ${unknown.map((/** @type {any} */ r) => `"${r}"`).join(', ')}; the rules are ${RULE_IDS.join(', ')}.`, selected: [] };
  if (!rules.length) return { status: 'inconclusive', scope: 'Nothing was checked.', explanation: 'The claim lists no data rule.', selected: [] };
  const only = Array.isArray(ev.records) ? new Set(ev.records) : typeof ev.records === 'string' ? new Set([ev.records]) : null;
  const scoped = only ? narrow(model, only) : model;
  const { findings, checked } = dataFindings(scoped);
  const mine = findings.filter((f) => rules.includes(f.rule));
  const selected = [...new Set([...(scoped.byKind.record ?? []), ...(scoped.byKind.copy ?? [])].map((e) => e.id))];
  const counts = rules.map((/** @type {DataRule} */ r) => `${r} ${checked[r]}`).join(', ');
  const scope = `Checked the ${(scoped.byKind.record ?? []).length} records and ${(scoped.byKind.copy ?? []).length} copies${only ? ` of ${[...only].join(', ')}` : ''} at this model revision against ${rules.length === 1 ? 'rule' : 'rules'} ${rules.join(', ')} (items checked per rule: ${counts}).${declaredMarkersLimit(rules)}`;
  if (mine.length) {
    const first = mine[0];
    return {
      status: 'violated', scope, selected,
      explanation: `${first.message}${mine.length > 1 ? ` ${mine.length - 1} more ${mine.length === 2 ? 'finding' : 'findings'}: ${mine.slice(1).map((f) => `${f.rule} on ${f.entityId}`).join(', ')}.` : ''}`,
      counterexample: { summary: mine.map((f) => `${f.rule}: ${f.entityId}${f.fields.length ? ` (${f.fields.join(', ')})` : ''}`).join('; '), entities: [...new Set(mine.flatMap((f) => [f.entityId, ...f.records]))] },
    };
  }
  const vacuous = rules.filter((/** @type {DataRule} */ r) => checked[r] === 0);
  if (vacuous.length) return { status: 'inconclusive', scope, selected, explanation: `Rule${vacuous.length === 1 ? '' : 's'} ${vacuous.join(', ')} had nothing to check in this model, so ${vacuous.length === 1 ? 'it holds' : 'they hold'} only vacuously. It is not reported as verified; list only the rules that apply.` };
  return { status: 'verified', scope, selected, explanation: `No finding: ${rules.map((/** @type {DataRule} */ r) => DATA_RULES[r].doc).join(' ')}` };
}

/**
 * A view of the model holding only the given records and the copies of them
 * (a copy keeps only the listed sources).
 * @param {Model} model @param {Set<string>} only @returns {Model}
 */
function narrow(model, only) {
  const records = (model.byKind.record ?? []).filter((r) => only.has(r.id));
  const copies = (model.byKind.copy ?? []).filter((c) => Array.isArray(c.data.of) && c.data.of.some((/** @type {any} */ id) => only.has(id)));
  return { ...model, byKind: { ...model.byKind, record: records, copy: copies } };
}

/**
 * The scope sentence for the rules that read only what the model declares about a field: a field counts as
 * personal data only when it declares `personal` or refers to the principal. A field that holds personal data
 * (an email address, say) without declaring it is invisible to these rules.
 * @param {DataRule[]} rules
 */
function declaredMarkersLimit(rules) {
  const reads = rules.filter((r) => r === 'erasure-point' || r === 'no-principal-in-shared');
  if (!reads.length) return '';
  return ` Rule${reads.length === 1 ? '' : 's'} ${reads.join(' and ')} read only the personal markers the model declares (a field's "personal" value or a reference to the principal): a field that holds personal data but declares neither is not seen, so the absence of a finding shows that the declared markers are absent from the copy, not that it holds no personal data.`;
}
