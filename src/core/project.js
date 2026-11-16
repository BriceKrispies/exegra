// The transactional project: the single place where a project's state changes.
//
// State = specification text + presentation layout text. The semantic model,
// diagnostics and hashes are derived from the specification text and replaced
// as a whole on every commit (immutable snapshots). A transaction is a list of
// operations applied all-or-nothing: if any operation fails its preconditions,
// or the resulting model has validation errors, nothing changes.

import { analyzeSpec } from './analyze.js';
import { semanticHash, hashString } from './hash.js';
import { OPERATIONS, OpError, Tx, parseLayout, EMPTY_LAYOUT } from './operations.js';
import { own } from './own.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {import('./types.js').Operation} Operation */
/** @typedef {import('./types.js').TransactionResult} TransactionResult */

/**
 * @typedef {Object} HistoryEntry
 * @property {number} revision          revision this entry produced
 * @property {string} label
 * @property {string} origin            ui | source | cli | external | undo | redo | import
 * @property {string[]} ops             operation type names
 * @property {string[]} affected
 * @property {boolean} semanticChanged
 * @property {boolean} specChanged
 * @property {boolean} layoutChanged
 * @property {string} hashBefore
 * @property {string} hashAfter
 */

export class Project {
  /**
   * @param {{specText: string, layoutText?: string|null, name?: string}} init
   */
  constructor(init) {
    this.name = init.name ?? '';
    this.specText = init.specText;
    this.layoutText = init.layoutText && parseLayout(init.layoutText).ok ? init.layoutText : EMPTY_LAYOUT;
    /** Monotonic counter: every committed transaction, undo, redo or reload increments it. */
    this.revision = 1;
    /** Increments only when the semantic hash changes. */
    this.semanticRevision = 1;
    /** @type {Model|null} */
    this.model = null;
    /** @type {Diagnostic[]} */
    this.diagnostics = [];
    this.errorCount = 0;
    this.semanticHash = '';
    this.layout = parseLayout(this.layoutText);
    /** @type {HistoryEntry[]} */
    this.history = [];
    /** @type {{specText: string, layoutText: string, entry: HistoryEntry}[]} */
    this.undoStack = [];
    /** @type {{specText: string, layoutText: string, entry: HistoryEntry}[]} */
    this.redoStack = [];
    /** @type {Set<(event: {type: string, result: TransactionResult, entry: HistoryEntry}) => void>} */
    this.listeners = new Set();
    this.#derive();
  }

  /**
   * Re-derive model, diagnostics and hash from the specification text.
   * @param {ReturnType<typeof analyzeSpec>} [analysis] the analysis of exactly this.specText, when the caller already has it
   */
  #derive(analysis) {
    const a = analysis ?? analyzeSpec(this.specText);
    this.model = a.model;
    this.diagnostics = a.diagnostics;
    this.errorCount = a.errorCount;
    this.semanticHash = semanticHash(a.model);
    this.layout = parseLayout(this.layoutText);
  }

  /** Identity of the exact text state, for optimistic concurrency across processes. */
  get textHash() {
    return hashString(this.specText) + '.' + hashString(this.layoutText);
  }

  get canUndo() { return this.undoStack.length > 0; }
  get canRedo() { return this.redoStack.length > 0; }

  /** @param {(event: {type: string, result: TransactionResult, entry: HistoryEntry}) => void} fn */
  subscribe(fn) {
    this.listeners.add(fn);
    return () => { this.listeners.delete(fn); };
  }

  /**
   * @param {string} code @param {string} message @param {Diagnostic[]} [diagnostics]
   * @returns {TransactionResult}
   */
  #fail(code, message, diagnostics = []) {
    return { ok: false, code, message, diagnostics, revision: this.revision, semanticHash: this.semanticHash, affected: [], semanticChanged: false };
  }

  /**
   * Apply operations atomically.
   * @param {Operation|Operation[]} ops
   * @param {{label?: string, origin?: string, expectRevision?: number, expectHash?: string}} [opts]
   *   expectRevision / expectHash: optimistic concurrency. The transaction is
   *   refused with code "revision.stale" when the project has moved on.
   * @returns {TransactionResult}
   */
  apply(ops, opts = {}) {
    const list = Array.isArray(ops) ? ops : [ops];
    if (!list.length) return this.#fail('op.empty', 'A transaction needs at least one operation.');
    if (opts.expectRevision !== undefined && opts.expectRevision !== this.revision) {
      return this.#fail('revision.stale', `The transaction was prepared against revision ${opts.expectRevision}, but the project is at revision ${this.revision}.`);
    }
    if (opts.expectHash !== undefined && opts.expectHash !== this.semanticHash) {
      return this.#fail('revision.stale', `The transaction was prepared against semantic hash ${opts.expectHash}, but the project is at ${this.semanticHash}.`);
    }
    for (const op of list) {
      if (!op || typeof op.type !== 'string' || !own(OPERATIONS, op.type)) return this.#fail('op.unknown', `Unknown operation type ${JSON.stringify(op?.type)}.`);
    }
    if (!this.model && list.some((op) => op.type !== 'ReplaceSource' && op.type !== 'ReplaceLayout')) {
      return this.#fail('model.unavailable', 'The current source has syntax errors; fix it in the source editor before applying other operations.', this.diagnostics);
    }
    const tx = new Tx(this.specText, this.layoutText, /** @type {Model} */ (this.model));
    try {
      for (const op of list) OPERATIONS[op.type].apply(tx, op);
    } catch (e) {
      if (e instanceof OpError) return this.#fail(e.code, e.message, e.diagnostics);
      throw e;
    }
    /** @type {ReturnType<typeof analyzeSpec>|undefined} */
    let analysis;
    if (tx.specEdited) {
      analysis = analyzeSpec(tx.specText);
      if (analysis.errorCount || !analysis.model) {
        return this.#fail('validation.failed', `Rejected: the result would have ${analysis.errorCount} validation error(s).`, analysis.diagnostics.filter((d) => d.severity === 'error'));
      }
    }
    if (tx.layoutEdited && !parseLayout(tx.layoutText).ok) return this.#fail('layout.invalid', 'Rejected: the layout would become unreadable.');
    return this.#commit(tx.specText, tx.layoutText, {
      label: opts.label ?? list.map((o) => o.type).join(', '),
      origin: opts.origin ?? 'ui',
      ops: list.map((o) => o.type),
      affected: [...tx.affected],
    }, true, analysis);
  }

  /**
   * @param {string} specText @param {string} layoutText
   * @param {{label: string, origin: string, ops: string[], affected: string[]}} meta
   * @param {boolean} recordUndo
   * @param {ReturnType<typeof analyzeSpec>} [analysis] analysis of `specText`, when already computed
   * @returns {TransactionResult}
   */
  #commit(specText, layoutText, meta, recordUndo, analysis) {
    const before = { specText: this.specText, layoutText: this.layoutText };
    const hashBefore = this.semanticHash;
    const specChanged = specText !== this.specText;
    const layoutChanged = layoutText !== this.layoutText;
    this.specText = specText;
    this.layoutText = layoutText;
    // A presentation-only commit leaves the specification text, and therefore the model, untouched.
    if (specChanged) this.#derive(analysis);
    else this.layout = parseLayout(this.layoutText);
    this.revision++;
    const semanticChanged = this.semanticHash !== hashBefore;
    if (semanticChanged) this.semanticRevision++;
    /** @type {HistoryEntry} */
    const entry = { revision: this.revision, ...meta, semanticChanged, specChanged, layoutChanged, hashBefore, hashAfter: this.semanticHash };
    this.history.push(entry);
    if (recordUndo) {
      this.undoStack.push({ ...before, entry });
      this.redoStack.length = 0;
    }
    /** @type {TransactionResult} */
    const result = { ok: true, diagnostics: this.diagnostics, revision: this.revision, semanticHash: this.semanticHash, affected: meta.affected, semanticChanged };
    for (const fn of this.listeners) fn({ type: 'commit', result, entry });
    return result;
  }

  /** @returns {TransactionResult|null} null when there is nothing to undo */
  undo() {
    const item = this.undoStack.pop();
    if (!item) return null;
    this.redoStack.push({ specText: this.specText, layoutText: this.layoutText, entry: item.entry });
    return this.#commit(item.specText, item.layoutText, { label: `Undo: ${item.entry.label}`, origin: 'undo', ops: item.entry.ops, affected: item.entry.affected }, false);
  }

  /** @returns {TransactionResult|null} null when there is nothing to redo */
  redo() {
    const item = this.redoStack.pop();
    if (!item) return null;
    this.undoStack.push({ specText: this.specText, layoutText: this.layoutText, entry: item.entry });
    return this.#commit(item.specText, item.layoutText, { label: `Redo: ${item.entry.label}`, origin: 'redo', ops: item.entry.ops, affected: item.entry.affected }, false);
  }

  /**
   * Adopt texts that changed outside this process (another editor, git, an agent).
   * Text with syntax errors is refused so the last valid model survives; the
   * caller receives the diagnostics and decides how to surface the conflict.
   * Adopting an external text clears both the undo and redo stacks and is not
   * itself undoable (undo would overwrite the newer file on disk); the reload is
   * still recorded in `history`.
   * @param {{specText?: string, layoutText?: string}} texts
   * @returns {TransactionResult}
   */
  reload(texts) {
    const specText = texts.specText ?? this.specText;
    const layoutText = texts.layoutText ?? this.layoutText;
    if (specText === this.specText && layoutText === this.layoutText) {
      return { ok: true, diagnostics: this.diagnostics, revision: this.revision, semanticHash: this.semanticHash, affected: [], semanticChanged: false };
    }
    if (specText !== this.specText) {
      const a = analyzeSpec(specText);
      if (!a.model) return this.#fail('reload.syntax', 'The file on disk has syntax errors; the last valid model is kept.', a.diagnostics);
    }
    const usableLayout = parseLayout(layoutText).ok ? layoutText : this.layoutText;
    const beforeData = new Map(this.model ? [...this.model.entities].map(([id, e]) => [id, JSON.stringify(e.data)]) : []);
    const after = analyzeSpec(specText).model;
    const affected = [];
    if (after) {
      for (const [id, e] of after.entities) if (beforeData.get(id) !== JSON.stringify(e.data)) affected.push(id);
      for (const id of beforeData.keys()) if (!after.entities.has(id)) affected.push(id);
    }
    // The reload is not undoable: undoing would write pre-reload text over the newer file on disk.
    this.undoStack.length = 0;
    this.redoStack.length = 0;
    return this.#commit(specText, usableLayout, { label: 'Reloaded from disk', origin: 'external', ops: ['Reload'], affected }, false);
  }
}
