// The model mutation protocol.
//
// Every change to a project - from the 3D scene, the inspector, the source
// editor or the agent CLI - is one of the operations below, applied through
// Project.apply() (project.js). An operation never touches the in-memory model
// directly: it computes source-preserving JSONC edits against the specification
// text (or the presentation layout text), and the model is re-derived from the
// edited text. That is what makes the text and the visual editors two views of
// one authority instead of two models kept in sync.

import { modify, applyEdits, parseTree, findNodeAtLocation } from 'jsonc-parser';
import { parseSpec } from './parse.js';
import { parseExpr, exprRefs } from './expr.js';
import { insertInArray } from './text-edit.js';
import { declarationSite, ownedBy } from './query.js';
import metamodel from './metamodel.json' with { type: 'json' };

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Operation} Operation */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

const ID_RE = new RegExp(metamodel.idPattern);
export const LAYOUT_VERSION = '0.1';
export const EMPTY_LAYOUT = `{\n  // Presentation only. Nothing in this file carries architectural meaning.\n  "exegraLayout": "${LAYOUT_VERSION}",\n  "views": {}\n}\n`;

export class OpError extends Error {
  /** @param {string} code @param {string} message @param {Diagnostic[]} [diagnostics] */
  constructor(code, message, diagnostics = []) {
    super(message);
    this.name = 'OpError';
    this.code = code;
    this.diagnostics = diagnostics;
  }
}

/**
 * Parse presentation layout text. Never throws; unusable text yields an empty layout.
 * @param {string} text
 * @returns {{views: Record<string, {positions: Record<string, [number, number]>}>, ok: boolean}}
 */
export function parseLayout(text) {
  /** @type {import('jsonc-parser').ParseError[]} */
  const errors = [];
  const root = parseTree(text, errors, { allowTrailingComma: true });
  /** @type {Record<string, {positions: Record<string, [number, number]>}>} */
  const views = {};
  if (!root || errors.length || root.type !== 'object') return { views, ok: false };
  const viewsNode = findNodeAtLocation(root, ['views']);
  for (const prop of viewsNode?.type === 'object' ? viewsNode.children ?? [] : []) {
    const [k, v] = prop.children ?? [];
    if (!k || !v) continue;
    /** @type {Record<string, [number, number]>} */
    const positions = {};
    const posNode = findNodeAtLocation(v, ['positions']);
    for (const pp of posNode?.type === 'object' ? posNode.children ?? [] : []) {
      const [pk, pv] = pp.children ?? [];
      const a = pv?.type === 'array' ? pv.children ?? [] : [];
      if (pk && a.length === 2 && typeof a[0].value === 'number' && typeof a[1].value === 'number') positions[pk.value] = [a[0].value, a[1].value];
    }
    views[k.value] = { positions };
  }
  return { views, ok: true };
}

/**
 * Remove the array element or object property at `path` by cutting exactly its
 * own text (plus one separating comma), so that neighbouring declarations keep
 * their formatting and comments. Returns null when the path does not exist.
 * @param {string} text @param {(string|number)[]} path
 * @returns {string|null}
 */
export function removeAt(text, path) {
  const root = parseTree(text, [], { allowTrailingComma: true });
  if (!root || !path.length) return null;
  const parent = findNodeAtLocation(root, path.slice(0, -1));
  const last = path[path.length - 1];
  if (!parent) return null;
  const siblings = parent.children ?? [];
  let index = -1;
  if (parent.type === 'array' && typeof last === 'number') index = last < siblings.length ? last : -1;
  else if (parent.type === 'object') index = siblings.findIndex((p) => p.children?.[0]?.value === last);
  if (index < 0) return null;
  const node = siblings[index];
  let start = node.offset;
  let end = node.offset + node.length;
  /** Skip whitespace and comments; return the index of the next significant character. @param {number} i */
  const skip = (i) => {
    for (;;) {
      while (i < text.length && /\s/.test(text[i])) i++;
      if (text.startsWith('//', i)) { const nl = text.indexOf('\n', i); i = nl < 0 ? text.length : nl; }
      else if (text.startsWith('/*', i)) { const c = text.indexOf('*/', i); i = c < 0 ? text.length : c + 2; }
      else return i;
    }
  };
  const lineStart = text.lastIndexOf('\n', start - 1) + 1;
  const ownLine = /^[ \t]*$/.test(text.slice(lineStart, start));
  if (index < siblings.length - 1) {
    const comma = skip(end);
    if (text[comma] === ',') end = comma + 1;
    if (ownLine) {
      start = lineStart;
      const rest = /^[ \t]*\r?\n/.exec(text.slice(end));
      if (rest) end += rest[0].length;
      else while (text[end] === ' ' || text[end] === '\t') end++;
    } else while (text[end] === ' ' || text[end] === '\t') end++;
  } else if (index > 0) {
    const prev = siblings[index - 1];
    start = prev.offset + prev.length;
  }
  return text.slice(0, start) + text.slice(end);
}

/**
 * Working state of one transaction: the two texts being edited and the model
 * derived from the current specification text.
 */
export class Tx {
  /** @param {string} specText @param {string} layoutText @param {Model} model */
  constructor(specText, layoutText, model) {
    this.specText = specText;
    this.layoutText = layoutText;
    this.model = model;
    /** @type {Set<string>} */
    this.affected = new Set();
    this.specEdited = false;
    this.layoutEdited = false;
  }

  /** @param {string} text */
  #fmt(text) {
    return { formattingOptions: { insertSpaces: true, tabSize: 2, eol: text.includes('\r\n') ? '\r\n' : '\n' } };
  }

  /** Re-derive the model after an edit. */
  refresh() {
    const { model } = parseSpec(this.specText);
    if (!model) throw new OpError('edit.syntax', 'The edit would leave the specification syntactically invalid.');
    this.model = model;
  }

  /**
   * Set or remove (value undefined) the value at a JSON path of the specification.
   * @param {(string|number)[]} path @param {any} value @param {boolean} [insert] array insertion at the index
   */
  setSpec(path, value, insert = false) {
    const removed = value === undefined ? removeAt(this.specText, path) : null;
    if (removed !== null) this.specText = removed;
    else {
      const edits = modify(this.specText, path, value, { ...this.#fmt(this.specText), isArrayInsertion: insert });
      this.specText = applyEdits(this.specText, edits);
    }
    this.specEdited = true;
    this.refresh();
  }

  /**
   * Append (or insert at `index`) into an array, creating the array when absent.
   * @param {(string|number)[]} arrayPath @param {any} value @param {number} [index]
   */
  appendSpec(arrayPath, value, index) {
    const root = parseTree(this.specText, [], { allowTrailingComma: true });
    const node = root ? findNodeAtLocation(root, arrayPath) : undefined;
    if (!node) return this.setSpec(arrayPath, [value]);
    if (node.type !== 'array') throw new OpError('edit.not-array', `"${arrayPath.join('.')}" is not an array.`);
    const len = node.children?.length ?? 0;
    this.specText = insertInArray(this.specText, node, index === undefined ? len : Math.max(0, Math.min(index, len)), value);
    this.specEdited = true;
    this.refresh();
  }

  /** @param {(string|number)[]} path @param {any} value */
  setLayout(path, value) {
    const edits = modify(this.layoutText, path, value, this.#fmt(this.layoutText));
    this.layoutText = applyEdits(this.layoutText, edits);
    this.layoutEdited = true;
  }

  /** @param {string} id @param {string} [kind] @returns {Entity} */
  entity(id, kind) {
    const e = this.model.entities.get(id);
    if (!e) throw new OpError('entity.unknown', `No entity has id "${id}".`);
    if (kind && e.kind !== kind) throw new OpError('entity.kind', `"${id}" is a ${e.kind}, not a ${kind}.`);
    return e;
  }

  /** @param {any} id */
  requireFreshId(id) {
    if (typeof id !== 'string' || !ID_RE.test(id)) throw new OpError('id.format', `Id ${JSON.stringify(id)} must be lower-case words joined by hyphens.`);
    if (this.model.entities.has(id)) throw new OpError('id.duplicate', `Id "${id}" is already used by a ${this.model.entities.get(id)?.kind}.`);
  }
}

/** @param {any} v @param {string} name */
function requireString(v, name) {
  if (typeof v !== 'string' || !v) throw new OpError('op.param', `Operation parameter "${name}" must be a non-empty string.`);
  return v;
}

/** @param {any} property @returns {(string|number)[]} */
function propertyPath(property) {
  const path = Array.isArray(property) ? property : typeof property === 'string' ? property.split('.').map((s) => (/^\d+$/.test(s) ? Number(s) : s)) : null;
  if (!path || !path.length) throw new OpError('op.param', 'Operation parameter "property" must be a property name, a dotted path or a path array.');
  return path;
}

/**
 * What deleting an entity entails: the entities removed with it and the
 * references elsewhere that must be repaired. Pure; used both by DeleteEntity
 * and by editors that want to warn before deleting.
 * @param {Model} model @param {string} id
 * @returns {{entities: string[], repairs: {from: string, path: (string|number)[], action: 'remove'|'unset'|'reparent', value?: string, offset: number}[], dependents: {id: string, kind: string, via: string}[]}}
 */
export function planDelete(model, id) {
  /** @type {Set<string>} */
  const doomed = new Set();
  /** @type {Map<string, {from: string, path: (string|number)[], action: 'remove'|'unset'|'reparent', value?: string, offset: number}>} */
  const repairs = new Map();
  /** @type {Map<string, {id: string, kind: string, via: string}>} */
  const dependents = new Map();
  const queue = [id];
  while (queue.length) {
    const cur = /** @type {string} */ (queue.pop());
    if (doomed.has(cur)) continue;
    const entity = model.entities.get(cur);
    if (!entity) continue;
    doomed.add(cur);
    for (const o of ownedBy(model, cur)) doomed.add(o.id);
  }
  // Iterate to a fixed point: cascading deletions can expose further references.
  let changed = true;
  while (changed) {
    changed = false;
    for (const ref of model.refs) {
      if (!doomed.has(ref.target) || doomed.has(ref.from)) continue;
      const from = model.entities.get(ref.from);
      if (!from) continue;
      const rel = ref.path.slice(from.path.length);
      const via = rel.filter((s) => typeof s === 'string').join('.');
      if (!dependents.has(from.id + '|' + via)) dependents.set(from.id + '|' + via, { id: from.id, kind: from.kind, via });
      const last = rel[rel.length - 1];
      let lastIndex = -1;
      rel.forEach((s, i) => { if (typeof s === 'number') lastIndex = i; });
      if (typeof last === 'number') {
        repairs.set(JSON.stringify(ref.path), { from: from.id, path: ref.path, action: 'remove', offset: ref.loc.offset });
      } else if (lastIndex >= 0) {
        const p = ref.path.slice(0, from.path.length + lastIndex + 1);
        repairs.set(JSON.stringify(p), { from: from.id, path: p, action: 'remove', offset: ref.loc.offset });
      } else if (from.kind === 'component' && rel.length === 1 && rel[0] === 'parent') {
        const target = model.entities.get(ref.target);
        let up = target?.data.parent;
        while (typeof up === 'string' && doomed.has(up)) up = model.entities.get(up)?.data.parent;
        repairs.set(JSON.stringify(ref.path), typeof up === 'string' ? { from: from.id, path: ref.path, action: 'reparent', value: up, offset: ref.loc.offset } : { from: from.id, path: ref.path, action: 'unset', offset: ref.loc.offset });
      } else {
        const def = model.meta.entities[from.kind]?.properties[String(rel[0])];
        if (def?.required) {
          doomed.add(from.id);
          for (const o of ownedBy(model, from.id)) doomed.add(o.id);
          changed = true;
        } else {
          repairs.set(JSON.stringify(ref.path), { from: from.id, path: ref.path, action: 'unset', offset: ref.loc.offset });
        }
      }
    }
      // Expressions name behaviors textually (e.g. "worker.acked"); a declaration
    // whose expression names a removed behavior cannot survive it.
    for (const x of model.exprs) {
      if (doomed.has(x.owner)) continue;
      const parsed = parseExpr(x.src);
      if (!parsed.ok) continue;
      const hit = exprRefs(parsed.ast).find((path) => path.length > 1 && doomed.has(path[0]) && model.entities.get(path[0])?.kind === 'behavior');
      if (!hit) continue;
      const owner = model.entities.get(x.owner);
      if (!owner) continue;
      dependents.set(owner.id + '|expression', { id: owner.id, kind: owner.kind, via: 'expression' });
      doomed.add(owner.id);
      for (const o of ownedBy(model, owner.id)) doomed.add(o.id);
      changed = true;
    }
  }
  const live = [...repairs.values()].filter((r) => !doomed.has(r.from));
  return { entities: [...doomed], repairs: live, dependents: [...dependents.values()].filter((d) => d.id !== id) };
}

/**
 * @typedef {Object} OperationDef
 * @property {string} doc
 * @property {Record<string, string>} params
 * @property {string[]} preconditions
 * @property {string} effects
 * @property {'spec'|'layout'|'spec+layout'} persistence
 * @property {boolean} semantic   false when the operation can never change semantic content
 * @property {(tx: Tx, op: Operation) => void} apply
 */

/** @param {Tx} tx @param {string} kind @param {any} data @param {string} [owner] @param {number} [index] */
function createEntity(tx, kind, data, owner, index) {
  if (!tx.model.meta.entities[kind] || kind === 'system') throw new OpError('op.kind', `Cannot create an entity of kind "${kind}".`);
  if (!data || typeof data !== 'object' || Array.isArray(data)) throw new OpError('op.param', 'Operation parameter "data" must be an object.');
  tx.requireFreshId(data.id);
  const site = declarationSite(tx.model, kind);
  if (!site) throw new OpError('op.kind', `Entities of kind "${kind}" have no declaration site.`);
  if (site.section) {
    if (owner) throw new OpError('op.param', `A ${kind} is declared at top level and takes no "owner".`);
    tx.appendSpec([site.section], data, index);
  } else {
    const o = tx.entity(requireString(owner, 'owner'), site.ownerKind);
    tx.appendSpec([...o.path, /** @type {string} */ (site.property)], data, index);
    tx.affected.add(o.id);
  }
  tx.affected.add(data.id);
}

/** @param {Tx} tx @param {string} id @param {boolean} cascade */
function deleteEntity(tx, id, cascade) {
  const target = tx.entity(id);
  if (target.kind === 'system') throw new OpError('delete.system', 'The system entity cannot be deleted.');
  const plan = planDelete(tx.model, id);
  if (plan.dependents.length && !cascade) {
    throw new OpError('delete.referenced', `"${id}" is referenced by ${plan.dependents.length} other declaration(s). Delete with cascade to remove or repair them.`,
      plan.dependents.map((d) => {
        const e = /** @type {Entity} */ (tx.model.entities.get(d.id));
        return { code: 'delete.dependent', severity: /** @type {'error'} */ ('error'), message: `${e.kind} "${e.id}" refers to "${id}" through "${d.via}".`, entityId: e.id, loc: e.loc, path: e.path };
      }));
  }
  // Edit from the end of the document backwards so earlier paths stay valid.
  /** @type {{path: (string|number)[], offset: number, value: any}[]} */
  const edits = [];
  for (const eid of plan.entities) {
    const e = /** @type {Entity} */ (tx.model.entities.get(eid));
    if (e.owner && plan.entities.includes(e.owner)) continue; // removed with its owner
    edits.push({ path: e.path, offset: e.loc.offset, value: undefined });
  }
  for (const r of plan.repairs) edits.push({ path: r.path, offset: r.offset, value: r.action === 'reparent' ? r.value : undefined });
  edits.sort((a, b) => b.offset - a.offset);
  const done = [];
  for (const e of edits) {
    const key = JSON.stringify(e.path);
    if (done.some((d) => key.startsWith(d.slice(0, -1) + ','))) continue; // inside something already removed
    tx.setSpec(e.path, e.value);
    if (e.value === undefined) done.push(key);
  }
  for (const r of plan.repairs) tx.affected.add(r.from);
  for (const eid of plan.entities) tx.affected.add(eid);
  const layout = parseLayout(tx.layoutText);
  for (const [view, v] of Object.entries(layout.views)) {
    for (const eid of plan.entities) if (v.positions[eid]) tx.setLayout(['views', view, 'positions', eid], undefined);
  }
}

/** @type {Record<string, OperationDef>} */
export const OPERATIONS = {
  CreateEntity: {
    doc: 'Declare a new entity of any kind except system.',
    params: { kind: 'entity kind', data: 'the declaration, including a fresh "id"', owner: 'owning entity id (ports, states, transitions only)', index: 'optional position among siblings' },
    preconditions: ['kind is a known entity kind', 'data.id is well-formed and unused', 'owner exists and is of the owning kind when the kind is nested'],
    effects: 'One new declaration in the specification. All of its references must resolve or the transaction is rejected.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => createEntity(tx, requireString(op.kind, 'kind'), op.data, op.owner, op.index),
  },
  DeleteEntity: {
    doc: 'Remove an entity. Without cascade it fails when anything refers to the entity; with cascade the referrers are repaired or removed.',
    params: { id: 'entity id', cascade: 'boolean, default false' },
    preconditions: ['the entity exists and is not the system', 'no other declaration refers to it, unless cascade is true'],
    effects: 'The entity and everything it owns are removed. With cascade: list references are dropped, optional references are unset, children of a removed subsystem move to its parent, and declarations that cannot exist without the entity are removed too. Layout positions of removed entities are discarded.',
    persistence: 'spec+layout', semantic: true,
    apply: (tx, op) => deleteEntity(tx, requireString(op.id, 'id'), op.cascade === true),
  },
  RenameEntity: {
    doc: 'Change the stable id of an entity and rewrite every reference to it. (To change a display name, use SetProperty on "name".)',
    params: { id: 'current id', newId: 'new id' },
    preconditions: ['the entity exists', 'newId is well-formed and unused'],
    effects: 'The declaration, every reference, every expression that names the entity and every layout position follow the new id. Semantic content is otherwise unchanged.',
    persistence: 'spec+layout', semantic: true,
    apply: (tx, op) => {
      const id = requireString(op.id, 'id');
      const entity = tx.entity(id);
      tx.requireFreshId(op.newId);
      const refs = tx.model.refs.filter((r) => r.target === id);
      const exprs = tx.model.exprs.filter((x) => x.src.includes(id));
      tx.setSpec([...entity.path, 'id'], op.newId);
      for (const r of refs) { tx.setSpec(r.path, op.newId); tx.affected.add(r.from); }
      for (const x of exprs) {
        const parsed = parseExpr(x.src);
        if (!parsed.ok) continue;
        /** @type {number[]} */
        const hits = [];
        const walk = (/** @type {any} */ n) => {
          if (n.t === 'ref') { if (n.path.length > 1 && n.path[0] === id) hits.push(n.pos); }
          else if (n.t === 'un') walk(n.a);
          else if (n.t === 'bin') { walk(n.a); walk(n.b); }
        };
        walk(parsed.ast);
        if (!hits.length) continue;
        let src = x.src;
        for (const pos of hits.sort((a, b) => b - a)) src = src.slice(0, pos) + op.newId + src.slice(pos + id.length);
        tx.setSpec(x.path, src);
        tx.affected.add(x.owner);
      }
      const layout = parseLayout(tx.layoutText);
      for (const [view, v] of Object.entries(layout.views)) {
        if (!v.positions[id]) continue;
        tx.setLayout(['views', view, 'positions', op.newId], v.positions[id]);
        tx.setLayout(['views', view, 'positions', id], undefined);
      }
      tx.affected.add(id);
      tx.affected.add(op.newId);
    },
  },
  SetProperty: {
    doc: 'Set, replace or remove one property of an entity.',
    params: { id: 'entity id', property: 'property name, dotted path ("implementation.status") or path array', value: 'new JSON value; null removes the property' },
    preconditions: ['the entity exists', 'the property is not "id"'],
    effects: 'Exactly one value in the declaration changes. The value must satisfy the meta-model or the transaction is rejected.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => {
      const entity = tx.entity(requireString(op.id, 'id'));
      const path = propertyPath(op.property);
      if (path.length === 1 && path[0] === 'id') throw new OpError('op.param', 'Use RenameEntity to change an id.');
      tx.setSpec([...entity.path, ...path], op.value === null ? undefined : op.value);
      tx.affected.add(entity.id);
    },
  },
  CreateRelationship: {
    doc: 'Connect two components or ports with a typed relationship.',
    params: { kind: 'relationship kind', from: 'source component or port id', to: 'target component or port id', id: 'optional id (derived when omitted)', description: 'optional', label: 'optional' },
    preconditions: ['kind is a known relationship kind', 'from and to identify components or ports'],
    effects: 'One new relationship declaration.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => {
      const from = requireString(op.from, 'from');
      const to = requireString(op.to, 'to');
      const kind = requireString(op.kind, 'kind');
      let id = op.id;
      if (id === undefined) {
        const base = `${from}-${kind}-${to}`;
        id = base;
        for (let n = 2; tx.model.entities.has(id); n++) id = `${base}-${n}`;
      }
      /** @type {Record<string, any>} */
      const data = { id, kind, from, to };
      if (typeof op.label === 'string' && op.label) data.label = op.label;
      if (typeof op.description === 'string' && op.description) data.description = op.description;
      createEntity(tx, 'relationship', data);
    },
  },
  DeleteRelationship: {
    doc: 'Remove a relationship.',
    params: { id: 'relationship id', cascade: 'boolean, default false' },
    preconditions: ['the entity exists and is a relationship'],
    effects: 'Same as DeleteEntity, restricted to relationships.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => { tx.entity(requireString(op.id, 'id'), 'relationship'); deleteEntity(tx, op.id, op.cascade === true); },
  },
  MovePresentationNode: {
    doc: 'Place (or reset) an entity in one view. Presentation only.',
    params: { view: 'view id', id: 'entity id', x: 'number', z: 'number', reset: 'true to return the entity to automatic layout' },
    preconditions: ['the entity exists', 'x and z are finite numbers unless reset is true'],
    effects: 'Only the layout file changes. The semantic hash of the model is unaffected by construction: this operation cannot edit the specification text.',
    persistence: 'layout', semantic: false,
    apply: (tx, op) => {
      const view = requireString(op.view, 'view');
      const entity = tx.entity(requireString(op.id, 'id'));
      if (op.reset === true) {
        if (parseLayout(tx.layoutText).views[view]?.positions[entity.id]) tx.setLayout(['views', view, 'positions', entity.id], undefined);
      } else {
        if (!Number.isFinite(op.x) || !Number.isFinite(op.z)) throw new OpError('op.param', '"x" and "z" must be finite numbers.');
        tx.setLayout(['views', view, 'positions', entity.id], [Math.round(op.x * 100) / 100, Math.round(op.z * 100) / 100]);
      }
      tx.affected.add(entity.id);
    },
  },
  AddClaim: {
    doc: 'Declare a claim.',
    params: { data: 'claim declaration with id, kind, statement and evaluate' },
    preconditions: ['data.id is well-formed and unused'],
    effects: 'One new claim. It is not evaluated by being declared.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => createEntity(tx, 'claim', op.data),
  },
  ModifyClaim: {
    doc: 'Change several properties of one claim atomically.',
    params: { id: 'claim id', changes: 'object of property -> new value (null removes)' },
    preconditions: ['the entity exists and is a claim', 'changes does not contain "id"'],
    effects: 'The listed properties change together or not at all. Earlier evaluation results no longer apply to the new revision.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => {
      const claim = tx.entity(requireString(op.id, 'id'), 'claim');
      if (!op.changes || typeof op.changes !== 'object' || 'id' in op.changes) throw new OpError('op.param', '"changes" must be an object of properties other than "id".');
      for (const [k, v] of Object.entries(op.changes)) tx.setSpec([...tx.entity(claim.id).path, k], v === null ? undefined : v);
      tx.affected.add(claim.id);
    },
  },
  AddState: {
    doc: 'Add a state to a behavior.',
    params: { behavior: 'behavior id', data: 'state declaration' },
    preconditions: ['the behavior exists', 'data.id is well-formed and unused'],
    effects: 'One new state in the behavior.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => createEntity(tx, 'state', op.data, op.behavior),
  },
  AddTransition: {
    doc: 'Add a transition to a behavior.',
    params: { behavior: 'behavior id', data: 'transition declaration', index: 'optional priority position' },
    preconditions: ['the behavior exists', 'data.id is well-formed and unused', 'from/to are states of that behavior', 'on is an event'],
    effects: 'One new transition. Transitions are tried in declaration order.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => createEntity(tx, 'transition', op.data, op.behavior, op.index),
  },
  ReplaceSource: {
    doc: 'Replace the whole specification text (used by the source editor and by imports).',
    params: { text: 'complete specification source' },
    preconditions: ['the text parses and validates without errors'],
    effects: 'The model becomes whatever the new text declares.',
    persistence: 'spec', semantic: true,
    apply: (tx, op) => {
      if (typeof op.text !== 'string') throw new OpError('op.param', '"text" must be a string.');
      const before = new Set(tx.model ? tx.model.entities.keys() : []);
      const { model, diagnostics } = parseSpec(op.text);
      if (!model) throw new OpError('validation.failed', 'The source text has syntax errors.', diagnostics);
      const beforeData = new Map(tx.model ? [...tx.model.entities].map(([id, e]) => [id, JSON.stringify(e.data)]) : []);
      tx.specText = op.text;
      tx.specEdited = true;
      tx.model = model;
      for (const [id, e] of model.entities) if (beforeData.get(id) !== JSON.stringify(e.data)) tx.affected.add(id);
      for (const id of before) if (!model.entities.has(id)) tx.affected.add(id);
    },
  },
  ReplaceLayout: {
    doc: 'Replace the whole presentation layout text (used by imports).',
    params: { text: 'complete layout source' },
    preconditions: ['the text is a valid layout document'],
    effects: 'Only presentation changes.',
    persistence: 'layout', semantic: false,
    apply: (tx, op) => {
      if (typeof op.text !== 'string' || !parseLayout(op.text).ok) throw new OpError('layout.invalid', 'The layout text is not a valid layout document.');
      tx.layoutText = op.text;
      tx.layoutEdited = true;
    },
  },
};
