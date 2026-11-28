// Targeted reads of a specification: get, find and refs. They answer from the semantic model
// (src/core/query.js, model.refs) with source locations, so an agent never has to open
// the specification text. Registered into the command table by cli/commands.js.
//
// The helpers of cli/commands.js are handed in (not imported) because commands.js imports this module.

/** @typedef {import('../src/core/types.js').Model} Model */
/** @typedef {import('../src/core/types.js').Entity} Entity */
/** @typedef {import('../src/core/types.js').Ref} Ref */
import { locate } from './locations.js';

export const DEFAULT_FIND_LIMIT = 100;

/**
 * Dotted property path of a reference, relative to the entity that holds it.
 * @param {Model} model @param {Ref} ref
 */
function relativePath(model, ref) {
  const from = model.entities.get(ref.from);
  return ref.path.slice(from ? from.path.length : 0).map(String).join('.');
}

/** @param {any} value @param {string} dotted */
export function valueAt(value, dotted) {
  let cur = value;
  for (const part of dotted.split('.')) {
    if (cur === null || typeof cur !== 'object' || !Object.hasOwn(cur, part)) return undefined;
    cur = cur[part];
  }
  return cur;
}

/**
 * Whether a value, or any element of an array value, prints as `expected`.
 * @param {any} value @param {string} expected
 * @returns {boolean}
 */
function valueMatches(value, expected) {
  if (Array.isArray(value)) return value.some((v) => valueMatches(v, expected));
  if (value === undefined || value === null || typeof value === 'object') return false;
  return String(value) === expected;
}

/**
 * Every string inside a value.
 * @param {any} value @param {string[]} [out]
 * @returns {string[]}
 */
function textsOf(value, out = []) {
  if (typeof value === 'string') out.push(value);
  else if (Array.isArray(value)) for (const v of value) textsOf(v, out);
  else if (value && typeof value === 'object') for (const v of Object.values(value)) textsOf(v, out);
  return out;
}

/**
 * Where an entity is declared.
 * @param {Entity} e @param {string|undefined} specFile
 */
function sourceOf(e, specFile) {
  const at = locate(e.loc, specFile);
  return { ...(at.file !== undefined ? { file: at.file } : {}), line: at.line, column: at.column };
}

/** Where a reference is written: the line, and for a specification kept as parts, the part file. @param {any} loc */
function lineOf(loc) {
  const at = locate(loc);
  return { ...(at.file !== undefined && loc?.file === undefined ? { file: at.file } : {}), line: at.line };
}

/** @param {Model} model @param {string} id */
export function outboundOf(model, id) {
  return model.refs.filter((r) => r.from === id).map((r) => ({ path: relativePath(model, r), target: r.target, ...lineOf(r.loc) }));
}

/** @param {Model} model @param {string} id */
export function inboundOf(model, id) {
  return model.refs.filter((r) => r.target === id).map((r) => ({ from: r.from, path: relativePath(model, r), ...lineOf(r.loc) }));
}

/**
 * @param {{loadProject: (ctx: any) => Promise<any>, requireModel: (p: any) => Model, requireEntity: (m: Model, id: string) => Entity,
 *   usage: (name: string, message: string) => Error, INLINE_OPTIONS: any, listValue: (v?: string) => string[], entityLabel: (e: Entity) => string}} h
 * @returns {Record<string, any>}
 */
export function readCommands(h) {
  /** @param {Entity} e @param {Model} model @param {string|undefined} specFile */
  const full = (e, model, specFile) => ({
    id: e.id,
    kind: e.kind,
    owner: e.owner ?? null,
    label: h.entityLabel(e),
    source: sourceOf(e, specFile),
    data: e.data,
    refersTo: outboundOf(model, e.id),
    referencedBy: inboundOf(model, e.id),
  });

  return {
    get: {
      usage: 'get <id> [<id> ...]',
      summary: 'Targeted read: the named entities with their declaration, owner, source file and line, and resolved references both ways.',
      options: { ...h.INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project, data } = await h.loadProject(ctx);
        const model = h.requireModel(project);
        if (ctx.positionals.length === 0) throw h.usage('missing-argument', 'Missing argument <id>.');
        const result = ctx.positionals.map((/** @type {string} */ id) => full(h.requireEntity(model, id), model, data?.spec?.path));
        return { result, semanticHash: project.semanticHash };
      },
    },

    find: {
      usage: 'find [--kind K] [--where prop=value]... [--refers-to ID] [--referenced-by ID] [--text "..."] [--fields a,b] [--limit N]',
      summary: 'Targeted search: entities matching every filter, with only the requested data fields (default: id, kind, label, source).',
      options: {
        kind: { type: 'string' },
        where: { type: 'string', multiple: true },
        'refers-to': { type: 'string' },
        'referenced-by': { type: 'string' },
        text: { type: 'string' },
        fields: { type: 'string' },
        limit: { type: 'string' },
        ...h.INLINE_OPTIONS,
      },
      run: async (/** @type {any} */ ctx) => {
        const { project, data } = await h.loadProject(ctx);
        const model = h.requireModel(project);
        const v = ctx.values;
        if (v.kind !== undefined && !model.meta.entities[v.kind]) throw h.usage('invalid-argument', `Unknown entity kind "${v.kind}".`);
        let limit = DEFAULT_FIND_LIMIT;
        if (v.limit !== undefined) {
          limit = Number(v.limit);
          if (!Number.isInteger(limit) || limit < 1) throw h.usage('invalid-argument', '--limit must be a positive integer.');
        }
        /** @type {{path: string, value: string}[]} */
        const wheres = (v.where ?? []).map((/** @type {string} */ w) => {
          const i = w.indexOf('=');
          if (i <= 0) throw h.usage('invalid-argument', `--where needs prop=value, got "${w}".`);
          return { path: w.slice(0, i), value: w.slice(i + 1) };
        });
        const fields = h.listValue(v.fields);
        if (v['refers-to'] !== undefined) h.requireEntity(model, v['refers-to']);
        if (v['referenced-by'] !== undefined) h.requireEntity(model, v['referenced-by']);
        const referrers = v['refers-to'] === undefined ? null : new Set(model.refs.filter((r) => r.target === v['refers-to']).map((r) => r.from));
        const referenced = v['referenced-by'] === undefined ? null : new Set(model.refs.filter((r) => r.from === v['referenced-by']).map((r) => r.target));
        const needle = v.text === undefined ? null : String(v.text).toLowerCase();

        /** @type {Entity[]} */
        const matches = [];
        for (const e of model.entities.values()) {
          if (v.kind !== undefined && e.kind !== v.kind) continue;
          if (referrers && !referrers.has(e.id)) continue;
          if (referenced && !referenced.has(e.id)) continue;
          if (!wheres.every((w) => valueMatches(valueAt(e.data, w.path), w.value))) continue;
          if (needle !== null && !textsOf(e.data).some((t) => t.toLowerCase().includes(needle))) continue;
          matches.push(e);
        }
        const entities = matches.slice(0, limit).map((e) => {
          /** @type {Record<string, any>} */
          const out = { id: e.id, kind: e.kind, label: h.entityLabel(e), source: sourceOf(e, data?.spec?.path) };
          if (fields.length) {
            /** @type {Record<string, any>} */
            const picked = {};
            for (const f of fields) picked[f] = valueAt(e.data, f) ?? null;
            out.fields = picked;
          }
          return out;
        });
        return {
          result: { total: matches.length, returned: entities.length, truncated: matches.length > entities.length, entities },
          semanticHash: project.semanticHash,
        };
      },
    },

    refs: {
      usage: 'refs <id>',
      summary: 'References of one entity: outbound (property path to target) and inbound (source and path), as model.refs holds them.',
      options: { ...h.INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project } = await h.loadProject(ctx);
        const model = h.requireModel(project);
        const id = ctx.positionals[0];
        if (id === undefined || id === '') throw h.usage('missing-argument', 'Missing argument <id>.');
        h.requireEntity(model, id);
        return { result: { id, outbound: outboundOf(model, id), inbound: inboundOf(model, id) }, semanticHash: project.semanticHash };
      },
    },
  };
}
