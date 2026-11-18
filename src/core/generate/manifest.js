// manifest.json: the machine-readable model manifest. This module also holds the
// small pure helpers every generator shares (text rendering, table cells, JSON
// and Markdown finishing), so that the rules live in exactly one place.

import { semanticHash } from '../hash.js';
import { stableStringify } from '../stable-json.js';
import { entityLabel } from '../query.js';
import { CLAIM_STATUSES } from '../claim-methods.js';

/** @typedef {import('../types.js').Model} Model */
/** @typedef {import('../types.js').Entity} Entity */

/**
 * Plain text for any declared value. Never returns "undefined" or "[object Object]".
 * @param {any} v
 * @returns {string}
 */
export function text(v) {
  if (v === undefined || v === null) return '';
  if (typeof v === 'string') return v;
  if (typeof v === 'object') return stableStringify(v) ?? '';
  return String(v);
}

/** Text on a single line: newlines become spaces. @param {any} v */
export function oneLine(v) {
  return text(v).replace(/\s*\n\s*/g, ' ').trim();
}

/** A Markdown table cell: single line, pipes escaped. @param {any} v */
export function mdCell(v) {
  return oneLine(v).replace(/\|/g, '\\|');
}

/** A Markdown table cell that shows "-" when there is nothing to show. @param {any} v */
export function cell(v) {
  const s = mdCell(v);
  return s === '' ? '-' : s;
}

/** A value used as a list: arrays as they are, anything else as empty. @param {any} v @returns {any[]} */
export function list(v) {
  return Array.isArray(v) ? v : [];
}

/**
 * Source position of an entity, or null when it has none.
 * @param {Entity|undefined} e
 * @returns {{line: number, column: number}|null}
 */
export function sourceOf(e) {
  return e?.loc ? { line: e.loc.line, column: e.loc.column } : null;
}

/**
 * Display name of the entity an id refers to; the id itself when it is unknown.
 * @param {Model} model @param {any} id
 */
export function nameOf(model, id) {
  const e = typeof id === 'string' ? model.entities.get(id) : undefined;
  return e ? oneLine(entityLabel(e)) : text(id);
}

/**
 * Full label of a claim status from CLAIM_STATUSES; the raw value when unknown.
 * @param {string} status
 */
export function statusLabel(status) {
  return Object.hasOwn(CLAIM_STATUSES, status) ? CLAIM_STATUSES[/** @type {keyof typeof CLAIM_STATUSES} */ (status)].label : text(status);
}

/** JSON artifact text: sorted keys, two-space indent, one trailing newline. @param {any} value */
export function json(value) {
  return stableStringify(value, 2) + '\n';
}

/**
 * Markdown artifact text from lines: one trailing newline, no trailing blank lines.
 * @param {string[]} lines
 */
export function markdown(lines) {
  return lines.join('\n').replace(/\s+$/, '') + '\n';
}

/**
 * The declaration of an entity without its nested entity arrays (ports, states,
 * transitions). Nested entities are listed on their own with `owner` set.
 * @param {Model} model @param {Entity} e
 */
function declaredData(model, e) {
  const props = model.meta.entities[e.kind]?.properties ?? {};
  /** @type {Record<string, any>} */
  const out = {};
  for (const [k, v] of Object.entries(e.data ?? {})) {
    if (props[k]?.type === 'entities') continue;
    out[k] = v;
  }
  return out;
}

/**
 * @param {Model} model
 * @returns {string} manifest.json text
 */
export function generateManifest(model) {
  const sys = model.system ?? model.byKind.system?.[0];
  const sd = sys?.data ?? {};

  /** @type {Record<string, number>} */
  const counts = {};
  for (const kind of Object.keys(model.meta.entities)) counts[kind] = (model.byKind[kind] ?? []).length;

  /** @type {Record<string, {label: string, shape: string, color: string}>} */
  const categories = {};
  for (const [id, c] of Object.entries(model.meta.categories ?? {})) {
    categories[id] = { label: text(/** @type {any} */ (c).label), shape: text(/** @type {any} */ (c).shape), color: text(/** @type {any} */ (c).color) };
  }

  /** @type {Record<string, {label: string, line: string, color: string, dependency: boolean}>} */
  const relationshipKinds = {};
  for (const [id, r] of Object.entries(model.meta.relationshipKinds ?? {})) {
    const k = /** @type {any} */ (r);
    relationshipKinds[id] = { label: text(k.label), line: text(k.line), color: text(k.color), dependency: k.dependency === true };
  }

  const entities = [...model.entities.values()].map((e) => ({
    id: e.id,
    kind: e.kind,
    owner: e.owner ?? null,
    label: oneLine(entityLabel(e)),
    source: sourceOf(e),
    data: declaredData(model, e),
  }));

  return json({
    format: 'exegra-manifest',
    version: 1,
    schemaVersion: model.schemaVersion,
    semanticHash: semanticHash(model),
    system: {
      id: sd.id ?? null,
      name: sd.name ?? null,
      version: sd.version ?? null,
      illustrative: sd.illustrative === true,
    },
    counts,
    vocabulary: { categories, relationshipKinds },
    entities,
  });
}
