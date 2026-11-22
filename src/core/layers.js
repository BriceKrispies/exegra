// A layered specification: the platform specification and product files beside it (WG-4989).
//
// A product file is its own JSONC document. Its "product" header names the product, the platform
// specification it builds on (`imports.spec`, a path relative to the product file) and the platform
// entities it uses (`imports.entities`, ids). The rest of the file is sections of entities, like a
// specification, restricted to what a product may add: tenant metadata (record types, views,
// workflows, operations, roles) and the claims, scenarios and journeys about them (ARC-113).
//
//   { "product": { "id": "badges", "name": "Badges",
//                  "imports": { "spec": "../spec.jsonc", "entities": ["tenant-id", "owner"] } },
//     "records": [ ... ], "screens": [ ... ] }
//
// This module stays ahead of the verified kernel: it checks each product file on its own, splices
// the entities of the sound sections into the platform text (the platform text itself is kept byte
// for byte, the product entities are appended at the end of their sections) and has the ordinary
// analysis (analyzeSpec, which derives the model in Lean) read the combined text. Every location
// the analysis reports is then mapped back to the file it came from (`loc.file` names a product
// file; a location without `file` is in the platform specification), and the diagnostics that mean
// something particular in a layered specification are restated with the rule that applies:
//
//   layer.header-missing, layer.header-invalid   the "product" header is absent or malformed
//   layer.import-mismatch                         imports.spec is not this project's platform file
//   layer.kind-not-allowed, layer.section-invalid a section a product may not declare, or not an array
//   layer.import-unknown                          an imported id the platform does not declare
//   layer.import-missing                          a platform entity used without being imported
//   layer.reference-unknown                       a reference no layer can resolve
//   layer.redefines-entity                        an id the platform (or another product) declares
//   layer.cross-product-reference                 a reference into another product file
//   layer.product-id-duplicate                    two product files with one product id
//   layer.entity-id-invalid, layer.entity-id-missing  a product entity id that fails the id pattern, or no id
//   layer.platform-power                          a product entity that claims what only the platform may have
//   layer.platform-references-product             a platform entity that names a product entity
//   layer.namespace-missing                       a product entity id outside the namespace of its product (D-6582)
//   layer.value-invalid, layer.outside-catalogue  a value in a typed section that does not conform to its platform
//                                                 type, or a union value the platform's union lacks (layer-values.js)
//   layer.reference-unknown, layer.cross-product-reference
//                                                 also for the names inside the typed sections
//   layer.expr-syntax, layer.expr-unknown-field, layer.expr-unknown-role, layer.expr-unknown-param, layer.expr-type
//                                                 an expression text of a typed section that does not parse or does
//                                                 not check in its scope (layer-expr.js, WG-5060)
//   layer.retention-missing                       an object type with a personal field and no retention (D-6584)
//
// The typed sections (objects, policies, segments, settings, ledgerUnits, ledgerPools, ledgerLimits,
// mailTemplates, noticeTemplates, tokens, triggers, automations, operations) are not entities of the
// specification format: they are not spliced into the combined text, and layer-values.js checks each
// value against its platform type. The platform's semantic hash is the hash of the platform text parsed alone, so adding a product
// file never changes it (and never changes what is generated from the platform); the hash of the
// combined model is reported beside it as the layered hash.

import { parseTree, printParseErrorCode, findNodeAtLocation, getNodeValue } from 'jsonc-parser';
import metamodel from './metamodel.json' with { type: 'json' };
import { parseSpec } from './parse.js';
import { analyzeSpec } from './analyze.js';
import { parseTypeName } from './codegen-model.js';
import { TYPED_SECTIONS, typedSection, checkTypedItem, namespaceOf, NAMESPACE_SEPARATOR } from './layer-values.js';
import { checkExpressionText, expressionScope, productContext } from './layer-expr.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {import('./types.js').Loc} Loc */
/** @typedef {import('jsonc-parser').Node} JsonNode */

/**
 * One product file as the caller read it. `platform` is what the caller (who can resolve paths)
 * found about `product.imports.spec`: the path it declares, whether it is this project's platform
 * file, and the path that would be (relative to the product file). Without `platform` the import
 * path is not checked.
 * @typedef {{file: string, text: string, platform?: {declared: string|null, matches: boolean, expected: string}}} ProductLayer
 */

/** The header key of a product file. */
export const PRODUCT_HEADER = 'product';

/**
 * The entity sections a product file may declare (entities of the specification format), and what each
 * is for. ARC-113: a product module adds record types, views, workflows and operations as tenant
 * metadata, with no change to the kernel. Its permissions are roles over platform capabilities; the one
 * platform section a product adds to is its own capabilities (D-6590). The typed sections, whose
 * values conform to platform types, are TYPED_SECTIONS (layer-values.js).
 */
export const PRODUCT_SECTIONS = Object.freeze({
  records: 'record types',
  types: 'the value types of its records and operations',
  screens: 'views',
  forms: 'views',
  actions: 'views',
  liveBindings: 'views',
  errorMessages: 'views',
  behaviors: 'workflows',
  events: 'workflows',
  contracts: 'operations',
  roles: 'roles (over platform capabilities)',
  scenarios: 'scenarios about its own entities',
  uiScenarios: 'journeys about its own entities',
  claims: 'claims about its own entities',
  evidence: 'evidence of its claims',
  capabilities: 'capabilities (names that tenant roles grant; each id in the namespace of the product, D-6590)',
});

/** Every section a product file may declare: the entity sections, then the typed sections. */
export const PRODUCT_SECTION_NAMES = Object.freeze([...Object.keys(PRODUCT_SECTIONS), ...TYPED_SECTIONS.map((t) => t.section)]);

/** Why a section of the specification format is not one a product may declare. @type {Record<string, string>} */
const REFUSED_BECAUSE = {
  exegra: 'The schema version is the platform specification\'s; remove it.',
  system: 'The system is the platform\'s; remove it.',
  vocabulary: 'The vocabulary is the platform\'s, and a product must not change how the platform is read; remove it.',
};
const PLATFORM_CODE = 'It is platform code or structure: a product refers to the platform\'s by id (list them in product.imports.entities) and does not declare its own. If the product truly needs a new one, it belongs in the platform specification.';

const ID_RE = new RegExp(metamodel.idPattern);
const HEADER_KEYS = new Set(['id', 'name', 'description', 'imports', 'version', 'platform']);

/** A version of a product: three whole numbers joined by dots (specc layers.rs is_version). @param {any} v */
const isVersion = (v) => typeof v === 'string' && /^[0-9]{1,9}.[0-9]{1,9}.[0-9]{1,9}$/.test(v);
/** A platform release: one to three whole numbers joined by dots, optionally a hyphen and a label (is_release). @param {any} v */
const isRelease = (v) => typeof v === 'string' && /^[0-9]{1,9}(.[0-9]{1,9}){0,2}(-[A-Za-z0-9.]+)?$/.test(v);
/** The numbers of a release without its trailing zeros: 0.2 and 0.2.0 are one release (release_numbers). @param {string} release */
function releaseNumbers(release) {
  const numbers = release.split('-')[0].split('.').map(Number);
  while (numbers.length > 0 && numbers[numbers.length - 1] === 0) numbers.pop();
  return numbers;
}
/** @param {number[]} a @param {number[]} b */
function compareNumbers(a, b) {
  for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] < b[i] ? -1 : 1;
  return Math.sign(a.length - b.length);
}

/**
 * The problems of the platform range of a product header: an object with a "min" that is a platform release and,
 * when it excludes later releases, a "below" that is one too and is later than "min" (specc layers.rs platform_problems).
 * @param {string} file @param {any} value @returns {string[]}
 */
export function platformProblems(file, value) {
  const shape = '{"min": "<first release>", "below": "<first release it does not support>"}';
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return [`"product.platform" in ${file} must be an object ${shape}; correct it, or remove it for a product that states no platform range.`];
  /** @type {string[]} */
  const problems = [];
  for (const key of Object.keys(value)) if (key !== 'min' && key !== 'below') problems.push(`"product.platform" in ${file} has "${key}", which it does not take; it holds only min and below. Remove "${key}".`);
  /** @type {string[]} */
  const releases = [];
  for (const [key, required] of /** @type {[string, boolean][]} */ ([['min', true], ['below', false]])) {
    if (value[key] === undefined) { if (required) problems.push(`"product.platform" in ${file} has no "min", the first platform release the product supports; add it, as in ${shape}.`); }
    else if (isRelease(value[key])) releases.push(value[key]);
    else problems.push(`"product.platform.${key}" in ${file} must be a platform release such as "0.2" or "1.4.0" (whole numbers joined by dots); correct it.`);
  }
  if (releases.length === 2 && compareNumbers(releaseNumbers(releases[1]), releaseNumbers(releases[0])) <= 0) problems.push(`"product.platform" in ${file} excludes from "${releases[1]}", which is not later than its first release "${releases[0]}", so no release is supported; make "below" later than "min".`);
  return problems;
}
const JSONC = { allowTrailingComma: true, disallowComments: false };

/** @param {string} text */
function lineIndex(text) {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text.charCodeAt(i) === 10) starts.push(i + 1);
  return starts;
}

/** @param {number[]} starts @param {number} offset @param {number} length @returns {Loc} */
function locOf(starts, offset, length) {
  let lo = 0, hi = starts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (starts[mid] <= offset) lo = mid; else hi = mid - 1;
  }
  return { offset, length, line: lo + 1, column: offset - starts[lo] + 1 };
}

/** @param {string} code */
const humanize = (code) => code.replace(/([a-z])([A-Z])/g, '$1 $2').toLowerCase();

/** @param {JsonNode} prop @returns {[JsonNode, JsonNode]} */
const member = (prop) => /** @type {[JsonNode, JsonNode]} */ (prop.children);

/**
 * The entity of a layer, as found in its product file.
 * @typedef {{section: string, node: JsonNode, id: string|null}} LayerItem
 */

/**
 * @typedef {Object} LayerState
 * @property {ProductLayer} layer
 * @property {number[]} starts
 * @property {JsonNode|null} root
 * @property {JsonNode|null} header          the "product" object, when it is one
 * @property {string|null} productId
 * @property {JsonNode|null} productIdNode   the header's id node, when it is a well-formed id
 * @property {boolean} headerOk              id, name and imports are well-formed
 * @property {Map<string, JsonNode>} imports imported id -> its string node
 * @property {LayerItem[]} items             the entities of the sections it may declare
 */

/**
 * What the platform text alone determines: its parse (the Lean derivation of its model), its syntax tree
 * and its line index. None of it depends on the product files, so it is computed once per process for a
 * text and shared by every layered analysis of that text. The cached structures are deep-frozen (a Map
 * gets mutators that throw): a caller that tried to change them would fail loudly instead of corrupting
 * the next analysis.
 * @typedef {{parsed: {model: Model|null, diagnostics: Diagnostic[]}, root: JsonNode|null, starts: number[]}} BaseAnalysis
 */

const BASE_CACHE_SIZE = 2;
/** @type {Map<string, BaseAnalysis>} most recently used last */
const baseCache = new Map();
let baseAnalyses = 0;

/** @param {any} value @returns {any} */
function deepFreeze(value) {
  const seen = new Set();
  const stack = [value];
  const refuse = () => { throw new TypeError('The cached platform analysis is read-only.'); };
  while (stack.length) {
    const v = stack.pop();
    if (v === null || typeof v !== 'object' || seen.has(v)) continue;
    seen.add(v);
    if (v instanceof Map) {
      for (const [k, x] of v) stack.push(k, x);
      for (const m of ['set', 'delete', 'clear']) Object.defineProperty(v, m, { value: refuse });
    }
    for (const k of Object.keys(v)) stack.push(v[k]);
    Object.freeze(v);
  }
  return value;
}

/** @param {string} baseText @returns {BaseAnalysis} */
function baseAnalysis(baseText) {
  const hit = baseCache.get(baseText);
  if (hit) {
    baseCache.delete(baseText);
    baseCache.set(baseText, hit);
    return hit;
  }
  baseAnalyses++;
  const parsed = parseSpec(baseText);
  const root = parsed.model ? /** @type {JsonNode} */ (parseTree(baseText, [], JSONC)) : null;
  /** @type {BaseAnalysis} */
  const entry = deepFreeze({ parsed, root, starts: lineIndex(baseText) });
  baseCache.set(baseText, entry);
  while (baseCache.size > BASE_CACHE_SIZE) baseCache.delete(/** @type {string} */ (baseCache.keys().next().value));
  return entry;
}

/** How many platform texts analyzeLayers has parsed in this process (the rest were served from the cache). */
export const baseAnalysisCount = () => baseAnalyses;

/** Forget the cached platform analyses. */
export function clearBaseAnalysisCache() {
  baseCache.clear();
}

/**
 * Parse and validate a layered specification.
 *
 * `model` is the combined model (null when the platform text is unusable); `baseModel` the model of
 * the platform text alone, exactly what parseSpec gives for it; `baseHash` its semantic hash and
 * `layeredHash` that of the combined model. Diagnostics are the analysis of the combined model with
 * locations in their own files, and the layer rules; errorCount counts the errors as analyzeSpec does.
 *
 * @param {string} baseText the platform specification
 * @param {ProductLayer[]} layers the product files, in order
 * @returns {{model: Model|null, baseModel: Model|null, diagnostics: Diagnostic[], errorCount: number, baseHash: string, layeredHash: string, layers: {file: string, product: string|null, entities: string[]}[]}}
 */
export function analyzeLayers(baseText, layers) {
  const baseEntry = baseAnalysis(baseText);
  const base = baseEntry.parsed;
  if (!base.model) {
    const a = analyzeSpec(baseText, base);
    return { ...a, baseModel: null, baseHash: '00000000000000', layeredHash: '00000000000000', layers: layers.map((l) => ({ file: l.file, product: null, entities: [] })) };
  }
  const baseModel = base.model;
  /** @type {Diagnostic[]} */
  const layerDiags = [];
  const states = layers.map((layer) => readLayer(layer, layerDiags));

  // Splice the entities of every sound section into the platform text.
  const splice = spliceLayers(baseText, /** @type {JsonNode} */ (baseEntry.root), baseEntry.starts, states);
  const merged = analyzeSpec(splice.text);

  const fileOf = (/** @type {number} */ i) => (i < 0 ? undefined : layers[i].file);
  const startsOf = (/** @type {number} */ i) => (i < 0 ? splice.baseStarts : states[i].starts);
  /** @param {Loc|undefined} loc @returns {Loc|undefined} */
  const remapLoc = (loc) => {
    if (!loc) return loc;
    const s = splice.map(loc.offset);
    const e = loc.length > 0 ? splice.map(loc.offset + loc.length - 1) : s;
    const length = e.file === s.file && e.offset >= s.offset ? e.offset - s.offset + (loc.length > 0 ? 1 : 0) : 1;
    const out = locOf(startsOf(s.file), s.offset, length);
    const file = fileOf(s.file);
    return file === undefined ? out : { ...out, file };
  };
  /** @param {(string|number)[]|undefined} p @param {Loc|undefined} loc */
  const remapPath = (p, loc) => (p && loc?.file !== undefined ? splice.productPath(p) : p);

  const model = merged.model;
  if (model) {
    for (const e of model.entities.values()) {
      e.loc = /** @type {Loc} */ (remapLoc(e.loc));
      e.path = /** @type {(string|number)[]} */ (remapPath(e.path, e.loc));
    }
    for (const r of model.refs) {
      r.loc = /** @type {Loc} */ (remapLoc(r.loc));
      r.path = /** @type {(string|number)[]} */ (remapPath(r.path, r.loc));
    }
    for (const x of model.exprs) {
      x.loc = /** @type {Loc} */ (remapLoc(x.loc));
      x.path = /** @type {(string|number)[]} */ (remapPath(x.path, x.loc));
    }
  }

  /** @param {Loc|undefined} loc */
  const where = (loc) => (loc ? `${loc.file ?? 'the platform specification'}, line ${loc.line}` : 'an unknown place');
  /** @type {Diagnostic[]} */
  const diagnostics = [];
  for (const d of merged.diagnostics) {
    const loc = remapLoc(d.loc);
    /** @type {Diagnostic} */
    const out = { ...d, ...(loc ? { loc } : {}) };
    if (d.path) out.path = remapPath(d.path, loc);
    const inProduct = loc?.file !== undefined;
    if (d.code === 'id.duplicate' && d.entityId && model) {
      const first = model.entities.get(d.entityId);
      const fromPlatform = baseModel.entities.get(d.entityId);
      if (inProduct && fromPlatform) {
        out.code = 'layer.redefines-entity';
        out.message = `${loc.file} declares "${d.entityId}", but the platform specification already declares ${fromPlatform.kind} "${d.entityId}" (line ${fromPlatform.loc.line}). A product file cannot redefine or change a platform entity. Give the product's entity an id of its own (prefix it with the product id), or, to use the platform's ${fromPlatform.kind}, delete this declaration, list "${d.entityId}" in product.imports.entities and refer to it by id; to change the platform's ${fromPlatform.kind}, change the platform specification.`;
      } else if (inProduct && first && first.loc.file !== undefined && first.loc.file !== loc.file) {
        out.code = 'layer.redefines-entity';
        out.message = `${loc.file} declares "${d.entityId}", but product file ${first.loc.file} already declares ${first.kind} "${d.entityId}" (line ${first.loc.line}). Ids must be unique across the platform and every product file of a project; rename one of them (prefix it with its product id).`;
      } else if (first) {
        // The kernel names the line of the first declaration in the combined text; name it in its own file.
        out.message = `Id "${d.entityId}" is already used by a ${first.kind} declared at ${where(first.loc)}.`;
      }
    } else if (d.code === 'capability.unreachable' && inProduct) {
      // A product capability is entitled to a tenant by installing the product (D-6590), so no plan has to
      // entitle it and no product file can add a plan; only that a role or a grant confers it is checked.
      if (!d.message.includes('no role or grant confers it')) continue;
      out.message = `Capability "${d.entityId}" can never be used: no role or grant confers it.`;
    } else if (d.code === 'capability.unknown' && inProduct) {
      // The same rule as an id no layer declares (specc gives it for a capability named in a list).
      const name = /capability "([^"]+)"/.exec(d.message)?.[1];
      if (name !== undefined && !baseModel.entities.has(name)) {
        out.code = 'layer.reference-unknown';
        out.message = `${d.entityId ? `"${d.entityId}"` : 'An entity'} in ${loc.file} names the capability "${name}", which neither the platform specification nor this product file declares. If it is a platform capability, correct the id and list it in product.imports.entities; if it is one of this product's own capabilities, declare it in this file.`;
      }
    } else if (d.code === 'ref.unresolved' && inProduct) {
      out.code = 'layer.reference-unknown';
      const target = model?.refs.find((r) => r.loc.offset === loc.offset && r.loc.file === loc.file)?.target;
      out.message = `${d.entityId ? `"${d.entityId}"` : 'An entity'} in ${loc.file} refers to ${target ? `"${target}"` : 'an id'}, which neither the platform specification nor this product file declares (${d.message.replace(/\.$/, '')}). If it is a platform entity, correct the id and list it in product.imports.entities; if it is one of this product's own entities, declare it in this file.`;
    }
    diagnostics.push(out);
  }
  diagnostics.push(...layerDiags);
  diagnostics.push(...productIdRules(states), ...powerRules(baseModel, states), ...namespaceRules(states), ...typedRules(baseModel, states), ...retentionRules(states));
  if (model) diagnostics.push(...importRules(model, baseModel, states), ...platformIndependenceRules(model));

  const fileRank = new Map(layers.map((l, i) => [l.file, i + 1]));
  const rank = { error: 0, warning: 1, info: 2 };
  diagnostics.sort((a, b) => rank[a.severity] - rank[b.severity]
    || (fileRank.get(a.loc?.file ?? '') ?? 0) - (fileRank.get(b.loc?.file ?? '') ?? 0)
    || (a.loc?.offset ?? 0) - (b.loc?.offset ?? 0)
    || (a.code < b.code ? -1 : a.code > b.code ? 1 : 0));
  return {
    model,
    baseModel,
    diagnostics,
    errorCount: diagnostics.filter((d) => d.severity === 'error' && d.code !== 'integrity.violated').length,
    baseHash: /** @type {string} */ (baseModel.semanticHash),
    layeredHash: model?.semanticHash ?? '00000000000000',
    layers: states.map((s) => ({ file: s.layer.file, product: s.productId, entities: s.items.map((i) => i.id).filter((id) => id !== null) })),
  };
}

/**
 * Read one product file: syntax, header, sections. Its diagnostics are pushed to `out`.
 * @param {ProductLayer} layer @param {Diagnostic[]} out
 * @returns {LayerState}
 */
function readLayer(layer, out) {
  const starts = lineIndex(layer.text);
  /** @type {LayerState} */
  const st = { layer, starts, root: null, header: null, productId: null, productIdNode: null, headerOk: false, imports: new Map(), items: [] };
  /** @param {string} code @param {string} message @param {JsonNode|null} node @param {string} [entityId] */
  const report = (code, message, node, entityId) => {
    const loc = node ? locOf(starts, node.offset, node.length) : locOf(starts, 0, 0);
    out.push({ code, severity: 'error', message, loc: { ...loc, file: layer.file }, ...(entityId ? { entityId } : {}) });
  };
  /** @type {import('jsonc-parser').ParseError[]} */
  const errors = [];
  const root = parseTree(layer.text, errors, JSONC);
  for (const e of errors) {
    const code = printParseErrorCode(e.error);
    out.push({ code: `syntax.${code}`, severity: 'error', message: `Syntax error in ${layer.file}: ${humanize(code)}.`, loc: { ...locOf(starts, e.offset, Math.max(1, e.length)), file: layer.file } });
  }
  if (errors.length) return st;
  const headerShape = `{"product": {"id": "<product id>", "name": "<name>", "imports": {"spec": "<path of the platform specification, relative to this file>", "entities": ["<platform entity id>", ...]}}}`;
  if (!root || root.type !== 'object') {
    report('layer.header-missing', `${layer.file} is not a JSON object. A product file is an object that starts with the header ${headerShape}, followed by sections of entities.`, root ?? null);
    return st;
  }
  st.root = root;
  for (const prop of root.children ?? []) {
    const [k, v] = member(prop);
    const key = String(k.value);
    if (key === PRODUCT_HEADER) {
      if (st.header) report('layer.header-invalid', `${layer.file} has a second "product" header; keep one.`, k);
      else readHeader(st, v, report);
      continue;
    }
    if (!Object.hasOwn(PRODUCT_SECTIONS, key) && !typedSection(key)) {
      const allowed = PRODUCT_SECTION_NAMES.join(', ');
      const why = REFUSED_BECAUSE[key]
        ?? (Object.hasOwn(metamodel.sections, key) ? PLATFORM_CODE : 'It is not a section of the specification format either: remove it, or, if it is product data, model it as a record type.');
      report('layer.kind-not-allowed', `${layer.file} declares "${key}", which a product file may not declare. A product adds only tenant metadata with no change to the kernel (ARC-113), in these sections: ${allowed}. ${why}`, k);
      continue;
    }
    if (v.type !== 'array') {
      report('layer.section-invalid', `"${key}" in ${layer.file} must be an array of entities; write it as "${key}": [ { "id": ... }, ... ].`, v);
      continue;
    }
    for (const item of v.children ?? []) {
      const idProp = item.type === 'object' ? (item.children ?? []).find((p) => member(p)[0].value === 'id') : undefined;
      const idNode = idProp ? member(idProp)[1] : undefined;
      const itemId = idNode?.type === 'string' ? String(idNode.value) : null;
      if (itemId === null) report('layer.entity-id-missing', `An item of "${key}" in ${layer.file} has no "id" (or is not an object). Every entity is an object with an "id" of lower-case words joined by hyphens; add it, or remove the item.`, item);
      else if (!ID_RE.test(itemId)) report('layer.entity-id-invalid', `The id "${itemId}" of an entity in "${key}" of ${layer.file} does not match the id pattern ${metamodel.idPattern}; write it as lower-case words joined by hyphens, prefixed with the product id.`, idNode ?? null, itemId);
      st.items.push({ section: key, node: item, id: itemId });
    }
  }
  if (!st.header) report('layer.header-missing', `${layer.file} has no "product" header. A product file starts with ${headerShape}; add it.`, root);
  return st;
}

/**
 * Check the "product" header and record its id and imports.
 * @param {LayerState} st @param {JsonNode} v
 * @param {(code: string, message: string, node: JsonNode|null, entityId?: string) => void} report
 */
function readHeader(st, v, report) {
  const file = st.layer.file;
  st.header = v;
  if (v.type !== 'object') {
    report('layer.header-invalid', `"product" in ${file} must be an object {"id": ..., "name": ..., "imports": {"spec": ..., "entities": [...]}}.`, v);
    return;
  }
  /** @type {Map<string, JsonNode>} */
  const fields = new Map();
  for (const prop of v.children ?? []) {
    const [k, val] = member(prop);
    const key = String(k.value);
    if (!HEADER_KEYS.has(key)) report('layer.header-invalid', `The product header of ${file} has "${key}", which it does not take; it holds only id, name, description, version, platform and imports. Remove "${key}".`, k);
    fields.set(key, val);
  }
  const version = fields.get('version');
  if (version && !isVersion(getNodeValue(version))) report('layer.header-invalid', `"product.version" in ${file} is ${JSON.stringify(getNodeValue(version))}, which is not a version. A version is three whole numbers joined by dots, such as "1.0.0" (an upgrade is offered only to a greater one, D-6583); correct it, or remove it.`, version);
  const platform = fields.get('platform');
  if (platform) for (const message of platformProblems(file, getNodeValue(platform))) report('layer.header-invalid', message, platform);
  let ok = true;
  const id = fields.get('id');
  if (id?.type === 'string' && ID_RE.test(String(id.value))) { st.productId = String(id.value); st.productIdNode = id; }
  else {
    ok = false;
    report('layer.header-invalid', `"product.id" in ${file} must be a lower-case id such as "badges" (pattern ${metamodel.idPattern}); ${id ? 'correct it' : 'add it'}.`, id ?? v);
  }
  const name = fields.get('name');
  if (!(name?.type === 'string' && String(name.value).trim() !== '')) {
    ok = false;
    report('layer.header-invalid', `"product.name" in ${file} must be a non-empty string naming the product; ${name ? 'correct it' : 'add it'}.`, name ?? v);
  }
  const imports = fields.get('imports');
  if (imports?.type !== 'object') {
    report('layer.header-invalid', `"product.imports" in ${file} must be an object {"spec": "<path of the platform specification, relative to this file>", "entities": ["<platform entity id>", ...]}; ${imports ? 'correct it' : 'add it'}.`, imports ?? v);
    st.headerOk = false;
    return;
  }
  /** @type {Map<string, JsonNode>} */
  const imp = new Map();
  for (const prop of imports.children ?? []) {
    const [k, val] = member(prop);
    const key = String(k.value);
    if (key !== 'spec' && key !== 'entities') report('layer.header-invalid', `"product.imports" in ${file} has "${key}", which it does not take; it holds only spec and entities. Remove "${key}".`, k);
    imp.set(key, val);
  }
  const spec = imp.get('spec');
  if (!(spec?.type === 'string' && String(spec.value).endsWith('.jsonc'))) {
    ok = false;
    report('layer.header-invalid', `"product.imports.spec" in ${file} must name the platform specification as a path relative to this file, ending in .jsonc${st.layer.platform ? ` (here "${st.layer.platform.expected}")` : ''}; ${spec ? 'correct it' : 'add it'}.`, spec ?? imports);
  } else if (st.layer.platform && !st.layer.platform.matches) {
    report('layer.import-mismatch', `${file} imports the platform specification "${spec.value}", which is not this project's platform specification. Set "product.imports.spec" to "${st.layer.platform.expected}", or take ${file} out of the project's "products" if it belongs to another platform.`, spec);
  }
  const entities = imp.get('entities');
  if (entities?.type !== 'array') {
    ok = false;
    report('layer.header-invalid', `"product.imports.entities" in ${file} must be an array of the ids of the platform entities the product uses (possibly empty); ${entities ? 'correct it' : 'add it'}.`, entities ?? imports);
  } else {
    for (const e of entities.children ?? []) {
      if (e.type !== 'string') {
        ok = false;
        report('layer.header-invalid', `Every item of "product.imports.entities" in ${file} must be a platform entity id (a string); correct or remove this one.`, e);
        continue;
      }
      const key = String(e.value);
      if (st.imports.has(key)) report('layer.header-invalid', `${file} imports "${key}" twice; remove the second.`, e);
      else st.imports.set(key, e);
    }
  }
  st.headerOk = ok;
}

/**
 * The combined text: the platform text with the entities of the layers spliced in at the end of
 * their sections (a section the platform lacks is added at the end of the platform's object), and
 * the maps from the combined text back to the files.
 * @param {string} baseText @param {JsonNode} baseRoot @param {number[]} baseStarts @param {LayerState[]} states
 */
function spliceLayers(baseText, baseRoot, baseStarts, states) {
  /** @type {Map<string, JsonNode>} */
  const baseSections = new Map();
  for (const prop of baseRoot.children ?? []) {
    const [k, v] = member(prop);
    baseSections.set(String(k.value), v);
  }
  const rootProps = baseRoot.children ?? [];
  const rootEnd = rootProps.length ? rootProps[rootProps.length - 1].offset + rootProps[rootProps.length - 1].length : baseRoot.offset + 1;
  /** @type {{at: number, seq: number, pieces: {text: string, layer: number, src: number}[]}[]} */
  const inserts = [];
  /** section -> ranges of combined indices: [{start, count, layer}] (layer -1: the platform) */
  /** @type {Map<string, {start: number, count: number, layer: number}[]>} */
  const ranges = new Map();
  let seq = 0;
  for (const section of Object.keys(PRODUCT_SECTIONS)) {
    /** @type {{layer: number, node: JsonNode}[]} */
    const items = [];
    states.forEach((st, layer) => { for (const it of st.items) if (it.section === section) items.push({ layer, node: it.node }); });
    if (!items.length) continue;
    const existing = baseSections.get(section);
    if (existing && existing.type !== 'array') continue; // the platform's own structural error is reported for it
    const baseItems = existing?.children ?? [];
    /** @type {{start: number, count: number, layer: number}[]} */
    const r = [{ start: 0, count: baseItems.length, layer: -1 }];
    let index = baseItems.length;
    /** @type {{text: string, layer: number, src: number}[]} */
    const pieces = [];
    const glue = (/** @type {string} */ text) => pieces.push({ text, layer: -1, src: -1 });
    let at;
    let first = true;
    if (existing) {
      const last = baseItems[baseItems.length - 1];
      at = last ? last.offset + last.length : existing.offset + 1;
      first = !last;
    } else {
      at = rootEnd;
      glue(`${rootProps.length || seq > 0 ? ',' : ''}\n  ${JSON.stringify(section)}: [`);
    }
    for (const { layer, node } of items) {
      glue(first ? '\n    ' : ',\n    ');
      first = false;
      pieces.push({ text: states[layer].layer.text.slice(node.offset, node.offset + node.length), layer, src: node.offset });
      const prev = r[r.length - 1];
      if (prev.layer === layer) prev.count += 1;
      else r.push({ start: index, count: 1, layer });
      index += 1;
    }
    if (!existing) glue('\n  ]');
    ranges.set(section, r);
    inserts.push({ at, seq: seq++, pieces });
  }
  inserts.sort((a, b) => a.at - b.at || a.seq - b.seq);

  // Segments of the combined text: {m: start in the combined text, layer, src: start in its file, fixed}.
  /** @type {{m: number, layer: number, src: number, fixed: boolean}[]} */
  const segments = [];
  const parts = [];
  let m = 0;
  let cursor = 0;
  const push = (/** @type {string} */ text, /** @type {number} */ layer, /** @type {number} */ src, /** @type {boolean} */ fixed) => {
    if (!text.length) return;
    segments.push({ m, layer, src, fixed });
    parts.push(text);
    m += text.length;
  };
  for (const ins of inserts) {
    push(baseText.slice(cursor, ins.at), -1, cursor, false);
    cursor = ins.at;
    for (const p of ins.pieces) push(p.text, p.layer, p.layer < 0 ? ins.at : p.src, p.layer < 0);
  }
  push(baseText.slice(cursor), -1, cursor, false);
  if (!segments.length) segments.push({ m: 0, layer: -1, src: 0, fixed: false });

  return {
    text: parts.join(''),
    baseStarts,
    /** The file (-1: the platform) and offset in it of an offset of the combined text. @param {number} o */
    map(o) {
      let lo = 0, hi = segments.length - 1;
      while (lo < hi) {
        const mid = (lo + hi + 1) >> 1;
        if (segments[mid].m <= o) lo = mid; else hi = mid - 1;
      }
      const s = segments[lo];
      return { file: s.layer, offset: s.fixed ? s.src : s.src + (o - s.m) };
    },
    /** A JSON path of the combined document as the path in its product file. @param {(string|number)[]} p */
    productPath(p) {
      const r = typeof p[0] === 'string' ? ranges.get(p[0]) : undefined;
      if (!r || typeof p[1] !== 'number') return p;
      const i = /** @type {number} */ (p[1]);
      const range = r.find((x) => i >= x.start && i < x.start + x.count);
      if (!range || range.layer < 0) return p;
      // The index among the layer's own items of the section, counted over every range of that layer.
      let before = 0;
      for (const x of r) if (x.layer === range.layer && x.start < range.start) before += x.count;
      return [p[0], before + (i - range.start), ...p.slice(2)];
    },
  };
}

/**
 * The type names a type text mentions: the plain names inside list<T>, set<T>, option<T>,
 * shared<T> and map<K, V>.
 * @param {string} text @returns {string[]}
 */
function typeNames(text) {
  const p = parseTypeName(text);
  if (p.k === 'name') return p.name ? [p.name] : [];
  if (p.k === 'map') return [...typeNames(p.key), ...typeNames(p.value)];
  return typeNames(p.of);
}

/**
 * Calls `use(name, kind, path)` for each platform-style name an entity's data holds outside the
 * typed references: a type named in a `type` or `repr` text, a capability in a `capabilities` or
 * `requires` list.
 * @param {any} value @param {(name: string, kind: string, path: (string|number)[]) => void} use @param {(string|number)[]} [p]
 */
function forEachNamedUse(value, use, p = []) {
  if (Array.isArray(value)) { value.forEach((v, i) => forEachNamedUse(v, use, [...p, i])); return; }
  if (value === null || typeof value !== 'object') return;
  for (const k of Object.keys(value)) {
    const v = value[k];
    if ((k === 'type' || k === 'repr') && typeof v === 'string') {
      for (const name of typeNames(v)) use(name, 'type', [...p, k]);
    } else if ((k === 'capabilities' || k === 'requires') && Array.isArray(v)) {
      v.forEach((c, i) => { if (typeof c === 'string') use(c, 'capability', [...p, k, i]); });
    } else forEachNamedUse(v, use, [...p, k]);
  }
}

/**
 * Two product files with one product id: the second is refused.
 * @param {LayerState[]} states @returns {Diagnostic[]}
 */
function productIdRules(states) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @type {Map<string, string>} */
  const first = new Map();
  for (const st of states) {
    if (st.productId === null || !st.productIdNode) continue;
    const other = first.get(st.productId);
    if (other === undefined) { first.set(st.productId, st.layer.file); continue; }
    out.push({
      code: 'layer.product-id-duplicate',
      severity: 'error',
      message: `${st.layer.file} has product id "${st.productId}", which product file ${other} already has. A product is one file; give this one a product id of its own, or merge the two files.`,
      loc: { ...locOf(st.starts, st.productIdNode.offset, st.productIdNode.length), file: st.layer.file },
    });
  }
  return out;
}

/** Holders only a platform role may have. */
const PLATFORM_HOLDERS = ['anonymous', 'service', 'external'];
/** Realisations that put server code behind a contract; only the platform declares those (a facade has none). */
const PLATFORM_REALISATIONS = ['generated', 'hand', 'derived'];

/**
 * What a product entity claims that only the platform may have: a platform-level role, anonymous,
 * service or external holders, a public anonymous contract, a contract implemented by a platform
 * component or realised in code, an implementation-level behavior, a domain, timer or
 * delivery-guaranteed event, a core capability, a setting at the platform level. A product adds tenant
 * metadata (ARC-113).
 * @param {Model} baseModel @param {LayerState[]} states @returns {Diagnostic[]}
 */
function powerRules(baseModel, states) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const st of states) {
    const file = st.layer.file;
    for (const it of st.items) {
      if (!['roles', 'contracts', 'behaviors', 'events', 'capabilities', 'settings'].includes(it.section)) continue;
      const data = getNodeValue(it.node);
      if (data === null || typeof data !== 'object' || Array.isArray(data)) continue;
      const id = it.id ?? '(no id)';
      /** @param {string} what @param {string} fix @param {(string|number)[]} p */
      const refuse = (what, fix, p) => {
        const node = findNodeAtLocation(it.node, p) ?? it.node;
        out.push({
          code: 'layer.platform-power',
          severity: 'error',
          message: `"${id}" in "${it.section}" of ${file} ${what}. A product adds tenant metadata only and cannot claim a power of the platform; ${fix}`,
          loc: { ...locOf(st.starts, node.offset, node.length), file },
          ...(it.id !== null ? { entityId: it.id } : {}),
        });
      };
      if (it.section === 'roles') {
        if (data.level === 'platform') refuse('has level "platform"', 'set level to "tenant": a product role is tenant data the tenant may change.', ['level']);
        (Array.isArray(data.holders) ? data.holders : []).forEach((/** @type {any} */ h, /** @type {number} */ i) => {
          if (PLATFORM_HOLDERS.includes(h)) refuse(`lets "${h}" hold it`, 'a product role is held by people, teams or agents; remove the holder, or declare the role in the platform specification.', ['holders', i]);
        });
      } else if (it.section === 'contracts') {
        if (data.exposure === 'public' && data.auth?.scheme === 'anonymous') refuse('is public with the anonymous scheme', "require a session (scheme \"session\") or make the contract internal; an anonymous public entry point is the platform's to declare.", ['auth', 'scheme']);
        if (typeof data.implementedBy === 'string' && baseModel.entities.get(data.implementedBy)?.kind === 'component') refuse(`is implemented by the platform component "${data.implementedBy}"`, 'a product contract is installed as tenant metadata and has no code of the platform behind it; remove implementedBy.', ['implementedBy']);
        if (PLATFORM_REALISATIONS.includes(data.realisation)) refuse(`declares realisation "${data.realisation}"`, 'only the platform puts code behind a contract; remove realisation (or use "facade").', ['realisation']);
      } else if (it.section === 'capabilities') {
        if (data.core === true) refuse('is a core capability', 'core capabilities are held by every tenant whatever its plan; a product capability is entitled by a plan like any other. Remove "core".', ['core']);
      } else if (it.section === 'settings') {
        if ((Array.isArray(data.levels) && data.levels.includes('platform')) || data['locked-by'] === 'platform') refuse('is set at, or locked by, the platform level', 'the platform level of a setting is the platform\'s; a product setting takes the levels tenant, team and person (D-6594).', ['levels']);
      } else if (it.section === 'behaviors') {
        if (data.level === 'implementation') refuse('has level "implementation"', 'a product behavior is a workflow model (level "model"); an implementation-level machine is platform code.', ['level']);
      } else {
        if (data.domain === true) refuse('is a domain event', 'domain events are facts the running platform records; remove "domain".', ['domain']);
        if (data.elapsed === true) refuse('is an elapsed-time event', 'timer events are implementation level; remove "elapsed".', ['elapsed']);
        if (data.delivery !== undefined) refuse('states a delivery guarantee', 'delivery is implementation level; remove "delivery".', ['delivery']);
      }
    }
  }
  return out;
}

/**
 * An entity id outside the namespace of its product: the product id with each hyphen replaced by an
 * underscore, followed by two underscores, and a local name (D-6582, D-6597).
 * @param {LayerState[]} states @returns {Diagnostic[]}
 */
function namespaceRules(states) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const st of states) {
    if (st.productId === null) continue;
    const ns = namespaceOf(st.productId);
    for (const it of st.items) {
      if (it.id === null || !ID_RE.test(it.id) || (it.id.startsWith(ns) && it.id !== ns)) continue;
      const idProp = (it.node.children ?? []).find((p) => member(p)[0].value === 'id');
      const node = idProp ? member(idProp)[1] : it.node;
      out.push({
        code: 'layer.namespace-missing',
        severity: 'error',
        message: `The id "${it.id}" of an entity in "${it.section}" of ${st.layer.file} is not in the namespace of its product (D-6582). Every id of product "${st.productId}" begins with "${ns}" followed by a local name; write it as "${ns}<local name>".`,
        loc: { ...locOf(st.starts, node.offset, node.length), file: st.layer.file },
        entityId: it.id,
      });
    }
  }
  return out;
}

/**
 * The typed sections: each value against its platform type (layer-values.js), the ids of the items
 * against the platform's and the other products', and the names inside the values against what the
 * products declare. A name with the namespace separator must be declared by the product file that holds
 * it, in a section its type allows; another product's entity is a cross-product reference; a name
 * without the separator names something outside the product and is not checked.
 * @param {Model} baseModel @param {LayerState[]} states @returns {Diagnostic[]}
 */
function typedRules(baseModel, states) {
  /** @type {Diagnostic[]} */
  const out = [];
  const typesOf = (/** @type {string} */ name) => {
    const e = baseModel.entities.get(name);
    return e?.kind === 'type' ? e.data : undefined;
  };
  /** id -> the file and section that declare it (first declaration). @type {Map<string, {file: string, section: string, typed: boolean}>} */
  const declared = new Map();
  for (const st of states) for (const it of st.items) if (it.id !== null && !declared.has(it.id)) declared.set(it.id, { file: st.layer.file, section: it.section, typed: typedSection(it.section) !== undefined });

  /** @type {Map<string, {file: string, typed: boolean}>} */
  const first = new Map();
  for (const st of states) {
    const file = st.layer.file;
    const ns = st.productId !== null && st.headerOk ? namespaceOf(st.productId) : null;
    /** What the expressions of this file may name; read when the first text is found. @type {import('./layer-expr.js').ProductContext|null} */
    let context = null;
    /** @param {string} code @param {string} message @param {JsonNode} node @param {string} entityId */
    const report = (code, message, node, entityId) => out.push({ code, severity: 'error', message, loc: { ...locOf(st.starts, node.offset, node.length), file }, entityId });
    for (const it of st.items) {
      if (it.id === null) continue;
      const typed = typedSection(it.section);
      const before = first.get(it.id);
      const platformDeclares = baseModel.entities.get(it.id);
      if (before === undefined) {
        first.set(it.id, { file, typed: typed !== undefined });
        if (typed && platformDeclares) report('layer.redefines-entity', `${file} declares "${it.id}" in "${it.section}", but the platform specification already declares ${platformDeclares.kind} "${it.id}". A product file cannot redefine or change a platform entity. Give the product's entity an id of its own (prefix it with the product id), or, to use the platform's, delete this declaration, list "${it.id}" in product.imports.entities and refer to it by id; to change the platform's, change the platform specification.`, it.node, it.id);
      } else if (typed || before.typed) {
        report('layer.redefines-entity', `${file} declares "${it.id}", but product file ${before.file} already declares it. Ids must be unique across the platform and every product file of a project; rename one of them (prefix it with its product id).`, it.node, it.id);
      }
      if (!typed) continue;
      const value = getNodeValue(it.node);
      const { problems, refs, exprs } = checkTypedItem(typesOf, file, typed, it.id, value);
      for (const p of problems) report(p.code, p.message, findNodeAtLocation(it.node, p.path) ?? it.node, it.id);
      for (const x of exprs) {
        context ??= productContext(baseModel, st.items.map((o) => ({ section: o.section, id: o.id, value: getNodeValue(o.node) })));
        const scope = expressionScope(context, it.section, value, x.path);
        const found = checkExpressionText(x.text, { ...scope, roles: context.roles, objects: context.objects });
        if (!found) continue;
        const at = x.path.length === 0 ? 'its value' : `"${x.path.join('.')}"`;
        const node = findNodeAtLocation(it.node, x.path) ?? it.node;
        report(found.code, `"${it.id}" in ${file}: the expression at ${at}, \`${x.text}\`, is refused at position ${found.pos}: ${found.message}. An expression in a product is text in the tenant rule language, checked against the object type, params and roles of the place it is written in; correct the text.`, node, it.id);
      }
      if (ns === null) continue;
      /** @type {Set<string>} */
      const seen = new Set();
      for (const r of refs) {
        const at = r.path.join('.');
        if (!r.name.includes(NAMESPACE_SEPARATOR) || baseModel.entities.has(r.name) || !seen.add(`${at}|${r.name}`)) continue;
        const node = findNodeAtLocation(it.node, r.path) ?? it.node;
        const wanted = r.sections.join(' or ');
        const target = declared.get(r.name);
        if (target && target.file === file) {
          if (!r.sections.includes(target.section)) report('layer.reference-unknown', `"${it.id}" in ${file} names "${r.name}" at ${at}, which the product declares in "${target.section}", but a name there is one declared in "${wanted}". Name an entity of the right kind, or declare "${r.name}" in "${wanted}".`, node, it.id);
        } else if (target) report('layer.cross-product-reference', `"${it.id}" in ${file} names "${r.name}" at ${at}, which product file ${target.file} declares. A product may name only platform entities and its own; move what is shared into the platform specification, or declare one under this product's own namespace.`, node, it.id);
        else report('layer.reference-unknown', `"${it.id}" in ${file} names "${r.name}" at ${at}, which no product file declares (a name in "${wanted}" is expected). Declare it in this file under that name, or correct the name.`, node, it.id);
      }
    }
  }
  return out;
}

/**
 * An object type with a field that declares personal data and no retention rule (D-6584). A type with a
 * personal field must carry the retention of its records; any other type takes the default of the tenant policy.
 * @param {LayerState[]} states @returns {Diagnostic[]}
 */
function retentionRules(states) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const st of states) {
    const file = st.layer.file;
    for (const it of st.items) {
      if (it.section !== 'objects' || it.id === null) continue;
      const data = getNodeValue(it.node);
      if (data === null || typeof data !== 'object' || Array.isArray(data) || (data.retention !== undefined && data.retention !== null)) continue;
      const fields = data.fields !== null && typeof data.fields === 'object' && !Array.isArray(data.fields) ? data.fields : {};
      const personal = Object.entries(fields).filter(([, f]) => f !== null && typeof f === 'object' && /** @type {any} */ (f).personal !== undefined && /** @type {any} */ (f).personal !== null).map(([name]) => name);
      if (!personal.length) continue;
      const node = findNodeAtLocation(it.node, ['fields', personal[0], 'personal']) ?? it.node;
      out.push({
        code: 'layer.retention-missing',
        severity: 'error',
        message: `The object type "${it.id}" in ${file} has the personal field${personal.length === 1 ? '' : 's'} ${personal.map((n) => `"${n}"`).join(', ')} and no retention (D-6584). A type with a personal field must say how long its records are kept; add "retention": { "days": <days>, "from": "Created" } (or "LastChanged", or { "Field": { "field": <a time field> } }) to the object type.`,
        loc: { ...locOf(st.starts, node.offset, node.length), file },
        entityId: it.id,
      });
    }
  }
  return out;
}

/**
 * A platform entity that names an entity a product file declares: the platform, and everything
 * generated from it, must not depend on a product. A name counts when it is a typed reference, a
 * type in a type text, or a capability in a capability list.
 * @param {Model} model @returns {Diagnostic[]}
 */
function platformIndependenceRules(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} from @param {string} target @param {string} at @param {Loc} loc */
  const report = (from, target, at, loc) => {
    const t = /** @type {Entity} */ (model.entities.get(target));
    out.push({
      code: 'layer.platform-references-product',
      severity: 'error',
      message: `The platform entity "${from}" refers to "${target}" (at ${at}), which product file ${t.loc.file} declares. The platform must not depend on a product: its text and everything generated from it are the same with or without product files. Remove the reference, or move "${target}" into the platform specification.`,
      loc,
      entityId: from,
    });
  };
  for (const r of model.refs) {
    if (r.loc.file !== undefined) continue;
    const target = model.entities.get(r.target);
    if (!target || target.loc.file === undefined) continue;
    const from = model.entities.get(r.from);
    report(r.from, r.target, (from ? r.path.slice(from.path.length) : r.path).map(String).join('.'), r.loc);
  }
  for (const e of model.entities.values()) {
    if (e.loc.file !== undefined) continue;
    forEachNamedUse(e.data, (name, kind, p) => {
      const t = model.entities.get(name);
      if (t && t.loc.file !== undefined && t.kind === kind) report(e.id, name, p.join('.'), e.loc);
    });
  }
  return out;
}

/**
 * The rules over the imports of each sound layer: an imported id the platform does not declare; a
 * platform entity used (by a reference, or by name as a type) without being imported; a reference
 * into another product file.
 * @param {Model} model @param {Model} baseModel @param {LayerState[]} states
 * @returns {Diagnostic[]}
 */
function importRules(model, baseModel, states) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const st of states) {
    if (!st.header) continue;
    const file = st.layer.file;
    /** @param {JsonNode} node */
    const at = (node) => ({ ...locOf(st.starts, node.offset, node.length), file });
    for (const [id, node] of st.imports) {
      if (baseModel.entities.has(id)) continue;
      const own = model.entities.get(id)?.loc.file === file;
      out.push({
        code: 'layer.import-unknown',
        severity: 'error',
        message: own
          ? `${file} imports "${id}", but that is this product's own entity, not a platform one; remove "${id}" from product.imports.entities.`
          : `${file} imports "${id}" (product.imports.entities), but the platform specification declares no entity with that id. Correct the id to one the platform declares, or remove it from product.imports.entities; if the product needs a new entity of its own, declare it in this file under an id of its own.`,
        loc: at(node),
      });
    }
    if (!st.headerOk) continue; // without a sound header the imports are unknown; the header error comes first
    for (const r of model.refs) {
      if (r.loc.file !== file) continue;
      const target = model.entities.get(r.target);
      if (!target || target.loc.file === file) continue;
      const from = model.entities.get(r.from);
      const via = from ? r.path.slice(from.path.length).map(String).join('.') : r.path.map(String).join('.');
      if (target.loc.file !== undefined) {
        out.push({
          code: 'layer.cross-product-reference',
          severity: 'error',
          message: `"${r.from}" in ${file} refers to "${r.target}" (at ${via}), which product file ${target.loc.file} declares. A product may refer only to platform entities and to its own; move the shared ${target.kind} into the platform specification, or declare one under this product's own id.`,
          loc: r.loc,
          entityId: r.from,
        });
      } else if (!st.imports.has(r.target)) {
        out.push({
          code: 'layer.import-missing',
          severity: 'error',
          message: `"${r.from}" in ${file} refers to the platform ${target.kind} "${r.target}" (at ${via}) without importing it. Add "${r.target}" to product.imports.entities, so that every platform entity the product depends on is listed in its header.`,
          loc: r.loc,
          entityId: r.from,
        });
      }
    }
    // Types are named in type texts and capabilities in id lists rather than by references; a platform type or
    // capability used by name is an import too.
    for (const it of st.items) {
      if (it.id === null || model.entities.get(it.id)?.loc.file !== file) continue;
      /** @type {Set<string>} */
      const seen = new Set();
      /** A platform entity of `kind` named by id at `p`, which must be imported. @param {string} name @param {string} kind @param {(string|number)[]} p */
      const use = (name, kind, p) => {
        const other = model.entities.get(name);
        if (kind === 'capability' && other?.kind === 'capability' && other.loc.file !== undefined && other.loc.file !== file && !seen.has(name)) {
          // A product capability is confined to its product (D-6590): another product file may not name it.
          seen.add(name);
          out.push({
            code: 'layer.cross-product-reference',
            severity: 'error',
            message: `"${it.id}" in ${file} names "${name}" at ${p.join('.')}, which product file ${other.loc.file} declares. A product may refer only to platform entities and to its own; move what is shared into the platform specification, or declare one under this product's own namespace.`,
            loc: at(findNodeAtLocation(it.node, p) ?? it.node),
            entityId: /** @type {string} */ (it.id),
          });
          return;
        }
        const t = baseModel.entities.get(name);
        if (!t || t.kind !== kind || st.imports.has(name) || seen.has(name)) return;
        seen.add(name);
        const node = findNodeAtLocation(it.node, p) ?? it.node;
        out.push({
          code: 'layer.import-missing',
          severity: 'error',
          message: `"${it.id}" in ${file} uses the platform ${kind} "${name}" (at ${p.join('.')}) without importing it. Add "${name}" to product.imports.entities, so that every platform entity the product depends on is listed in its header.`,
          loc: at(node),
          entityId: /** @type {string} */ (it.id),
        });
      };
      forEachNamedUse(/** @type {Entity} */ (model.entities.get(it.id)).data, use);
    }
  }
  return out;
}
