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

/** @param {string} text */
function fmt(text) {
  return { formattingOptions: { insertSpaces: true, tabSize: 2, eol: text.includes('\r\n') ? '\r\n' : '\n' } };
}

/**
 * Set or remove (value undefined) the value at a JSON path of a text: the one edit every
 * property change makes, whether on the whole specification or on one declaration's lines.
 * @param {string} text @param {(string|number)[]} path @param {any} value @param {boolean} insert
 */
function setAt(text, path, value, insert) {
  const removed = value === undefined ? removeAt(text, path) : null;
  if (removed !== null) return removed;
  return applyEdits(text, modify(text, path, value, { ...fmt(text), isArrayInsertion: insert }));
}

/**
 * Append (or insert at `index`) into the array at `arrayPath` of a text, creating the array when
 * absent. `pos` is where the value landed; `shifted` is true when it landed before existing items.
 * @param {string} text @param {(string|number)[]} arrayPath @param {any} value @param {number} [index]
 * @returns {{text: string, pos: number, shifted: boolean}}
 */
function appendAt(text, arrayPath, value, index) {
  const root = parseTree(text, [], { allowTrailingComma: true });
  const node = root ? findNodeAtLocation(root, arrayPath) : undefined;
  if (!node) return { text: setAt(text, arrayPath, [value], false), pos: 0, shifted: false };
  if (node.type !== 'array') throw new OpError('edit.not-array', `"${arrayPath.join('.')}" is not an array.`);
  const len = node.children?.length ?? 0;
  const pos = index === undefined ? len : Math.max(0, Math.min(index, len));
  return { text: insertInArray(text, node, pos, value), pos, shifted: pos < len };
}

/** @param {(string|number)[]} path */
const pathKey = (path) => JSON.stringify(path);

/**
 * Where an entity is declared: what operations look up mid-transaction (existence, kind, owner,
 * path) without re-deriving the model. Every model entity is one; so is an entity a transaction
 * has just declared.
 * @typedef {{id: string, kind: string, owner: string|null, path: (string|number)[]}} Declared
 */

/**
 * The full lines one top-level declaration occupies, edited on their own. `start` and `end` are
 * offsets in the base text (end at the line break, which stays outside).
 * @typedef {{start: number, end: number, text: string}} Window
 */

/**
 * Working state of one transaction: the two texts being edited and the model derived from the
 * specification text.
 *
 * The model is re-derived once per transaction, not once per operation. Between derivations the
 * transaction keeps an index of where every entity is declared (`Declared`), updated as operations
 * declare entities and invalidated by any edit that could change the set of entities, their kinds,
 * owners or paths; a lookup on an invalid index re-derives first. Operations that read references,
 * expressions or entity data (DeleteEntity, RenameEntity, ReplaceSource) read `model`, which
 * re-derives when the text changed since the last derivation. So every operation sees the effects
 * of the operations before it, as it did when the model was re-derived after every edit.
 *
 * Edits inside one top-level declaration are made on a window holding just its lines, and edits
 * that append to a section are kept as pending insertions; `specText` splices them into the base
 * text once. Every such edit is `jsonc-parser`'s `modify` (or `removeAt`, `insertInArray`), whose
 * result depends only on the edited lines when the text has no carriage returns, so the spliced
 * text is byte for byte the text the same edits make on the whole document. Anything else
 * (removing a whole declaration, a declaration sharing lines with others, a file with CRLF line
 * breaks) is edited on the whole text, as before.
 *
 * `eager` re-derives the model after every edit and edits only the whole text: the reference
 * behaviour the batched path is tested against. `diverged` becomes true when a derivation finds
 * that the index did not match the model it claimed to describe; Project.apply then replays the
 * transaction eagerly.
 */
export class Tx {
  /** Text the pending windows and insertions apply to. */
  #base = '';
  /** @type {import('jsonc-parser').Node|null|undefined} parse tree of #base, built on demand */
  #tree = undefined;
  /** @type {boolean|null} whether #base has no carriage return (windows are exact only then) */
  #plain = null;
  /** @type {Map<string, {node: import('jsonc-parser').Node, count: number}|null>} top-level arrays of #base */
  #sections = new Map();
  /** @type {Map<string, Window>} windows of declarations of #base, by "section\0index" */
  #windows = new Map();
  /** @type {Map<string, {at: number, items: {text: string}[]}>} declarations appended to a section, inserted at `at` */
  #appends = new Map();
  /** @type {Model|null} */
  #model = null;
  /** @type {{model: Model|null, diagnostics: Diagnostic[]}|null} the parse of the current text, when this transaction derived it */
  #parse = null;
  /** The text changed since #model was derived. */
  #dirty = false;
  /** @type {Map<string, Declared>} */
  #index = new Map();
  /** @type {Map<string, string>} entity id by path key */
  #byPath = new Map();
  #indexValid = false;
  /** @type {Set<string>|null} ids that more than one declaration uses, when known */
  #dupIds = null;
  #eager = false;

  /**
   * @param {string} specText @param {string} layoutText @param {Model} model the model of specText
   * @param {{eager?: boolean, diagnostics?: Diagnostic[]}} [opts] diagnostics: those of specText's
   *   parse (Project.diagnostics), which tell which ids are declared twice
   */
  constructor(specText, layoutText, model, opts = {}) {
    this.#base = specText;
    this.#eager = opts.eager === true;
    if (opts.diagnostics) this.#dupIds = duplicateIds(opts.diagnostics);
    this.layoutText = layoutText;
    if (model) this.#adopt(model);
    /** @type {Set<string>} */
    this.affected = new Set();
    this.specEdited = false;
    this.layoutEdited = false;
    this.diverged = false;
    /** How many times this transaction derived the model. */
    this.derivations = 0;
  }

  /** The current specification text. */
  get specText() {
    if (!this.#windows.size && !this.#appends.size) return this.#base;
    /** @type {[number, number, string][]} */
    const cuts = [];
    for (const w of this.#windows.values()) cuts.push([w.start, w.end, w.text]);
    for (const a of this.#appends.values()) cuts.push([a.at, a.at, a.items.map((it) => ',\n' + it.text).join('')]);
    cuts.sort((x, y) => x[0] - y[0] || x[1] - y[1]);
    const parts = [];
    let pos = 0;
    for (const [start, end, text] of cuts) {
      parts.push(this.#base.slice(pos, start), text);
      pos = end;
    }
    parts.push(this.#base.slice(pos));
    this.#rebase(parts.join(''));
    return this.#base;
  }

  /** Replace the whole specification text. */
  set specText(text) {
    this.#rebase(text);
    this.#dirty = true;
    this.#indexValid = false;
    this.#parse = null;
  }

  /** The model of the current specification text, re-derived when the text changed. */
  get model() {
    if (this.#dirty) this.#derive();
    return /** @type {Model} */ (this.#model);
  }

  /** Adopt a model the caller derived from the current specification text. */
  set model(model) {
    this.#adopt(model);
    this.#dirty = false;
    this.#parse = null;
    this.#dupIds = null;
  }

  /** The effective meta-model. Only a vocabulary edit changes it, and such an edit invalidates the index. */
  get meta() {
    this.#shape();
    return /** @type {Model} */ (this.#model).meta;
  }

  /** Re-derive the model now. */
  refresh() {
    this.#derive();
  }

  /**
   * The parse of the current specification text when this transaction derived it (so an analysis
   * need not parse it again), else null. Re-derives first when the text changed.
   * @returns {{model: Model|null, diagnostics: Diagnostic[]}|null}
   */
  parsed() {
    if (this.#dirty) this.#derive();
    return this.#parse;
  }

  /** @param {string} text */
  #rebase(text) {
    this.#base = text;
    this.#tree = undefined;
    this.#plain = null;
    this.#sections.clear();
    this.#windows.clear();
    this.#appends.clear();
  }

  /** @param {Model} model */
  #adopt(model) {
    this.#model = model;
    this.#index = new Map();
    this.#byPath = new Map();
    for (const e of model.entities.values()) {
      this.#index.set(e.id, e);
      this.#byPath.set(pathKey(e.path), e.id);
    }
    this.#indexValid = true;
  }

  #derive() {
    const parsed = parseSpec(this.specText);
    this.derivations++;
    if (!parsed.model) throw new OpError('edit.syntax', 'The edit would leave the specification syntactically invalid.');
    if (this.#indexValid && !this.#eager && !sameDeclarations(this.#index, parsed.model)) this.diverged = true;
    this.#adopt(parsed.model);
    this.#parse = parsed;
    this.#dupIds = duplicateIds(parsed.diagnostics);
    this.#dirty = false;
  }

  /** Make the index describe the current text. */
  #shape() {
    if (!this.#indexValid) this.#derive();
  }

  #invalidate() {
    this.#indexValid = false;
  }

  /**
   * Record an edit at `path` (value undefined: a removal) against the index, made the way the
   * model derivation would see it:
   * - inside a declared entity, below a property that declares no entities and is not its id:
   *   nothing changes;
   * - removing a declared entity from its array: it and everything nested in it go, and the
   *   items after it move up one;
   * - replacing or removing a property that declares entities: the old nested entities go and the
   *   new ones are declared;
   * - setting an entity's id: the entity and the owner of its nested entities follow.
   * Anything else invalidates the index. So does freeing an id that a duplicate declaration also
   * uses, since that declaration would then count.
   * @param {(string|number)[]} path @param {any} value @param {boolean} insert
   */
  #noteEdit(path, value, insert) {
    if (!this.#indexValid) return;
    const meta = /** @type {Model} */ (this.#model).meta;
    const exact = this.#byPath.get(pathKey(path));
    if (exact !== undefined) {
      const last = path[path.length - 1];
      if (value === undefined && !insert && typeof last === 'number' && this.#drop(path)) {
        this.#shift(path.slice(0, -1), last);
        return;
      }
      this.#invalidate();
      return;
    }
    for (let k = path.length - 1; k >= 1; k--) {
      const id = this.#byPath.get(pathKey(path.slice(0, k)));
      if (id === undefined) continue;
      const e = /** @type {Declared} */ (this.#index.get(id));
      const key = path[k];
      const def = meta.entities[e.kind]?.properties;
      const site = typeof key === 'string' && def && Object.hasOwn(def, key) && def[key]?.type === 'entities' ? def[key] : null;
      if (typeof key === 'string' && key !== 'id' && !site) return;
      if (k !== path.length - 1 || insert) break;
      if (key === 'id' && typeof value === 'string' && ID_RE.test(value) && !this.#index.has(value) && this.#frees([e.id])) {
        this.#rename(e, value);
        return;
      }
      if (site && this.#drop(path, true) && (value === undefined || (Array.isArray(value) && value.every((item, j) => this.#declareOne(site.entity, item, [...path, j], e.id))))) return;
      break;
    }
    this.#invalidate();
  }

  /**
   * Whether freeing these ids leaves the index exact: false when a duplicate declaration of one of
   * them exists, or when that cannot be known.
   * @param {string[]} ids
   */
  #frees(ids) {
    return this.#dupIds !== null && !ids.some((id) => /** @type {Set<string>} */ (this.#dupIds).has(id));
  }

  /**
   * Remove the entity at `path` and everything nested in it (or, with `below`, everything strictly
   * below `path`). False, with nothing removed, when an id freed this way has a duplicate.
   * @param {(string|number)[]} path @param {boolean} [below]
   */
  #drop(path, below = false) {
    const n = path.length;
    /** @type {Declared[]} */
    const gone = [];
    for (const d of this.#index.values()) {
      if (d.path.length < n + (below ? 1 : 0)) continue;
      let i = 0;
      while (i < n && d.path[i] === path[i]) i++;
      if (i === n) gone.push(d);
    }
    if (!this.#frees(gone.map((d) => d.id))) return false;
    for (const d of gone) {
      this.#index.delete(d.id);
      this.#byPath.delete(pathKey(d.path));
    }
    return true;
  }

  /**
   * Items after `removed` in the array at `arrayPath` move up one, with everything nested in them.
   * @param {(string|number)[]} arrayPath @param {number} removed
   */
  #shift(arrayPath, removed) {
    const n = arrayPath.length;
    /** @type {Declared[]} */
    const moved = [];
    for (const d of this.#index.values()) {
      const at = d.path[n];
      if (d.path.length <= n || typeof at !== 'number' || at <= removed) continue;
      let i = 0;
      while (i < n && d.path[i] === arrayPath[i]) i++;
      if (i === n) moved.push(d);
    }
    for (const d of moved) this.#byPath.delete(pathKey(d.path));
    for (const d of moved) {
      const path = [...d.path];
      path[n] = /** @type {number} */ (path[n]) - 1;
      const next = { id: d.id, kind: d.kind, owner: d.owner, path };
      this.#index.set(d.id, next);
      this.#byPath.set(pathKey(path), d.id);
    }
  }

  /** @param {Declared} e @param {string} newId */
  #rename(e, newId) {
    this.#index.delete(e.id);
    this.#index.set(newId, { id: newId, kind: e.kind, owner: e.owner, path: e.path });
    this.#byPath.set(pathKey(e.path), newId);
    for (const d of [...this.#index.values()]) {
      if (d.owner === e.id) this.#index.set(d.id, { id: d.id, kind: d.kind, owner: newId, path: d.path });
    }
  }

  /**
   * Add an entity the transaction declared, and the entities nested in it, to the index, the way
   * the model derivation would; invalidate the index when the declaration is anything but plain.
   * @param {string} kind @param {any} data @param {(string|number)[]} path @param {string|null} owner
   */
  #declare(kind, data, path, owner) {
    if (!this.#indexValid) return;
    if (!this.#declareOne(kind, data, path, owner)) this.#invalidate();
  }

  /** @param {string} kind @param {any} data @param {(string|number)[]} path @param {string|null} owner @returns {boolean} */
  #declareOne(kind, data, path, owner) {
    if (!data || typeof data !== 'object' || Array.isArray(data) || typeof data.id !== 'string' || this.#index.has(data.id)) return false;
    this.#index.set(data.id, { id: data.id, kind, owner, path });
    this.#byPath.set(pathKey(path), data.id);
    const props = /** @type {Model} */ (this.#model).meta.entities[kind]?.properties ?? {};
    for (const [key, def] of Object.entries(props)) {
      if (def?.type !== 'entities' || !Object.hasOwn(data, key) || data[key] === undefined) continue;
      const items = data[key];
      if (!Array.isArray(items)) return false;
      for (let j = 0; j < items.length; j++) if (!this.#declareOne(def.entity, items[j], [...path, key, j], data.id)) return false;
    }
    return true;
  }

  /** Edit the whole text. @param {(text: string) => string} edit */
  #whole(edit) {
    this.#rebase(edit(this.specText));
  }

  #isPlain() {
    if (this.#plain === null) this.#plain = !this.#base.includes('\r');
    return this.#plain;
  }

  /** @param {string} name */
  #section(name) {
    if (this.#sections.has(name)) return this.#sections.get(name) ?? null;
    if (this.#tree === undefined) this.#tree = parseTree(this.#base, [], { allowTrailingComma: true }) ?? null;
    const node = this.#tree ? findNodeAtLocation(this.#tree, [name]) : undefined;
    const sec = node?.type === 'array' ? { node, count: node.children?.length ?? 0 } : null;
    this.#sections.set(name, sec);
    return sec;
  }

  /**
   * The window of the top-level declaration `path` lies strictly inside, and the path within it;
   * null when the edit must be made on the whole text.
   * @param {(string|number)[]} path
   * @returns {{win: {text: string}, rel: (string|number)[]}|null}
   */
  #windowOf(path) {
    if (path.length < 3 || typeof path[0] !== 'string' || typeof path[1] !== 'number' || !this.#isPlain()) return null;
    const sec = this.#section(path[0]);
    if (!sec) return null;
    const i = path[1];
    const rel = path.slice(2);
    if (i < sec.count) {
      const key = `${path[0]}\u0000${i}`;
      let win = this.#windows.get(key);
      if (!win) {
        const opened = this.#open(/** @type {import('jsonc-parser').Node[]} */ (sec.node.children)[i], path[0]);
        if (!opened) return null;
        win = opened;
        this.#windows.set(key, win);
      }
      return { win, rel };
    }
    const app = this.#appends.get(path[0]);
    const item = app?.items[i - sec.count];
    return item ? { win: item, rel } : null;
  }

  /**
   * A window over the lines of one item of a section: only when nothing but indentation precedes
   * the item on its first line and nothing but a comma follows it on its last.
   * @param {import('jsonc-parser').Node} node @param {string} section
   * @returns {Window|null}
   */
  #open(node, section) {
    const t = this.#base;
    const start = t.lastIndexOf('\n', node.offset - 1) + 1;
    if (!/^[ \t]*$/.test(t.slice(start, node.offset))) return null;
    const nodeEnd = node.offset + node.length;
    let end = t.indexOf('\n', nodeEnd);
    if (end < 0) end = t.length;
    if (!/^[ \t]*,?[ \t]*$/.test(t.slice(nodeEnd, end))) return null;
    const at = this.#appends.get(section)?.at;
    if (at !== undefined && at > start && at < end) return null;
    return { start, end, text: t.slice(start, end) };
  }

  /**
   * Append a declaration at the end of a top-level section without touching the text before it,
   * the way insertInArray would. Returns the new item's index, or null when the append must be
   * made on the whole text.
   * @param {string} section @param {any} value @param {number} [index]
   * @returns {number|null}
   */
  #appendToSection(section, value, index) {
    if (!this.#isPlain()) return null;
    const sec = this.#section(section);
    if (!sec || !sec.count) return null;
    const items = /** @type {import('jsonc-parser').Node[]} */ (sec.node.children);
    let app = this.#appends.get(section);
    const len = sec.count + (app?.items.length ?? 0);
    if (index !== undefined && Math.max(0, Math.min(index, len)) < len) return null;
    if (!app) {
      const last = items[items.length - 1];
      const at = last.offset + last.length;
      if (at < this.#base.length && this.#base[at] !== '\n') return null;
      app = { at, items: [] };
      this.#appends.set(section, app);
    }
    const t = this.#base;
    // insertInArray's indentation: the first item's, else the array line's plus two spaces.
    const first = this.#windows.get(`${section}\u0000${0}`);
    let indent;
    if (first) indent = /^[ \t]*/.exec(first.text)?.[0] ?? '';
    else {
      const ls = t.lastIndexOf('\n', items[0].offset - 1) + 1;
      const lead = t.slice(ls, items[0].offset);
      if (/^[ \t]*$/.test(lead)) indent = lead;
      else {
        const als = t.lastIndexOf('\n', sec.node.offset - 1) + 1;
        indent = (/^[ \t]*/.exec(t.slice(als))?.[0] ?? '') + '  ';
      }
    }
    app.items.push({ text: indent + JSON.stringify(value, null, 2).split('\n').join('\n' + indent) });
    return len;
  }

  /**
   * Set or remove (value undefined) the value at a JSON path of the specification.
   * @param {(string|number)[]} path @param {any} value @param {boolean} [insert] array insertion at the index
   */
  setSpec(path, value, insert = false) {
    this.specEdited = true;
    if (this.#eager) {
      this.#whole((t) => setAt(t, path, value, insert));
      this.#derive();
      return;
    }
    this.#noteEdit(path, value, insert);
    const w = this.#windowOf(path);
    if (w) w.win.text = setAt(w.win.text, w.rel, value, insert);
    else this.#whole((t) => setAt(t, path, value, insert));
    this.#dirty = true;
  }

  /**
   * Append (or insert at `index`) into an array, creating the array when absent.
   * @param {(string|number)[]} arrayPath @param {any} value @param {number} [index]
   * @param {{kind: string, owner: string|null}} [declares] the entity `value` declares, so the index can follow
   */
  appendSpec(arrayPath, value, index, declares) {
    this.specEdited = true;
    if (this.#eager) {
      this.#whole((t) => appendAt(t, arrayPath, value, index).text);
      this.#derive();
      return;
    }
    /** @type {{pos: number, shifted: boolean}} */
    let r;
    const top = arrayPath.length === 1 && typeof arrayPath[0] === 'string' ? this.#appendToSection(arrayPath[0], value, index) : null;
    if (top !== null) r = { pos: top, shifted: false };
    else {
      const w = this.#windowOf(arrayPath);
      if (w) {
        const a = appendAt(w.win.text, w.rel, value, index);
        w.win.text = a.text;
        r = a;
      } else {
        /** @type {{pos: number, shifted: boolean}} */
        let a = { pos: 0, shifted: true };
        this.#whole((t) => { const x = appendAt(t, arrayPath, value, index); a = x; return x.text; });
        r = a;
      }
    }
    this.#dirty = true;
    if (!declares || r.shifted) this.#invalidate();
    else this.#declare(declares.kind, value, [...arrayPath, r.pos], declares.owner);
  }

  /** @param {(string|number)[]} path @param {any} value */
  setLayout(path, value) {
    const edits = modify(this.layoutText, path, value, fmt(this.layoutText));
    this.layoutText = applyEdits(this.layoutText, edits);
    this.layoutEdited = true;
  }

  /** @param {string} id @param {string} [kind] @returns {Declared} */
  entity(id, kind) {
    this.#shape();
    const e = this.#index.get(id);
    if (!e) throw new OpError('entity.unknown', `No entity has id "${id}".`);
    if (kind && e.kind !== kind) throw new OpError('entity.kind', `"${id}" is a ${e.kind}, not a ${kind}.`);
    return e;
  }

  /** Whether an entity has this id. @param {string} id */
  has(id) {
    this.#shape();
    return this.#index.has(id);
  }

  /** @param {any} id */
  requireFreshId(id) {
    if (typeof id !== 'string' || !ID_RE.test(id)) throw new OpError('id.format', `Id ${JSON.stringify(id)} must be lower-case words joined by hyphens.`);
    this.#shape();
    if (this.#index.has(id)) throw new OpError('id.duplicate', `Id "${id}" is already used by a ${this.#index.get(id)?.kind}.`);
  }

  /**
   * Whether the index still describes the text: re-derives when the text changed and reports a
   * mismatch through `diverged`. Used when a transaction fails, so that a failure caused by a
   * wrong index is replayed eagerly too.
   */
  check() {
    if (this.#dirty && this.#indexValid) {
      try { this.#derive(); } catch { /* the failure stands */ }
    }
    return !this.diverged;
  }
}

/**
 * The ids a parse reported as declared more than once.
 * @param {Diagnostic[]} diagnostics
 */
function duplicateIds(diagnostics) {
  return new Set(diagnostics.filter((d) => d.code === 'id.duplicate' && d.entityId).map((d) => /** @type {string} */ (d.entityId)));
}

/**
 * Whether an index holds exactly the entities of a model, each with the same kind, owner and path.
 * @param {Map<string, Declared>} index @param {Model} model
 */
function sameDeclarations(index, model) {
  if (index.size !== model.entities.size) return false;
  for (const e of model.entities.values()) {
    const d = index.get(e.id);
    if (!d || d.kind !== e.kind || (d.owner ?? null) !== (e.owner ?? null) || pathKey(d.path) !== pathKey(e.path)) return false;
  }
  return true;
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
  const meta = tx.meta;
  if (!meta.entities[kind] || kind === 'system') throw new OpError('op.kind', `Cannot create an entity of kind "${kind}".`);
  if (!data || typeof data !== 'object' || Array.isArray(data)) throw new OpError('op.param', 'Operation parameter "data" must be an object.');
  tx.requireFreshId(data.id);
  const site = declarationSite(/** @type {any} */ ({ meta }), kind);
  if (!site) throw new OpError('op.kind', `Entities of kind "${kind}" have no declaration site.`);
  if (site.section) {
    if (owner) throw new OpError('op.param', `A ${kind} is declared at top level and takes no "owner".`);
    tx.appendSpec([site.section], data, index, { kind, owner: null });
  } else {
    const o = tx.entity(requireString(owner, 'owner'), site.ownerKind);
    tx.appendSpec([...o.path, /** @type {string} */ (site.property)], data, index, { kind, owner: o.id });
    tx.affected.add(o.id);
  }
  tx.affected.add(data.id);
}

/** @param {Tx} tx @param {string} id @param {boolean} cascade */
function deleteEntity(tx, id, cascade) {
  const target = tx.entity(id);
  if (target.kind === 'system') throw new OpError('delete.system', 'The system entity cannot be deleted.');
  // The plan reads references and expressions, so it needs the model of the current text; the
  // edits below change the text, so the model is read once, before them.
  const model = tx.model;
  const plan = planDelete(model, id);
  if (plan.dependents.length && !cascade) {
    throw new OpError('delete.referenced', `"${id}" is referenced by ${plan.dependents.length} other declaration(s). Delete with cascade to remove or repair them.`,
      plan.dependents.map((d) => {
        const e = /** @type {Entity} */ (model.entities.get(d.id));
        return { code: 'delete.dependent', severity: /** @type {'error'} */ ('error'), message: `${e.kind} "${e.id}" refers to "${id}" through "${d.via}".`, entityId: e.id, loc: e.loc, path: e.path };
      }));
  }
  // Edit from the end of the document backwards so earlier paths stay valid.
  /** @type {{path: (string|number)[], offset: number, value: any}[]} */
  const edits = [];
  for (const eid of plan.entities) {
    const e = /** @type {Entity} */ (model.entities.get(eid));
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
      // References and expressions of the current text, read before the edits below change it.
      const model = tx.model;
      const refs = model.refs.filter((r) => r.target === id);
      const exprs = model.exprs.filter((x) => x.src.includes(id));
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
        for (let n = 2; tx.has(id); n++) id = `${base}-${n}`;
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
