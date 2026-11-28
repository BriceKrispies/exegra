// The transactional project: the single place where a project's state changes.
//
// State = specification text + presentation layout text. The semantic model,
// diagnostics and hashes are derived from the specification text and replaced
// as a whole on every commit (immutable snapshots). A transaction is a list of
// operations applied all-or-nothing: if any operation fails its preconditions,
// or the resulting model has validation errors, nothing changes.
//
// A layered project (WG-4989) also holds product files beside the platform
// specification (src/core/layers.js). Its model is the combined model, its
// semanticHash is the platform's alone (what is generated from the platform
// carries it) and layeredHash is that of the combined model. Transactions edit
// only the platform text; a product file is edited as a file.

import { analyzeSpec } from './analyze.js';
import { analyzeLayers } from './layers.js';
import { semanticHash } from './hash.js';
import { OPERATIONS, OpError, Tx, parseLayout, EMPTY_LAYOUT } from './operations.js';
import { own } from './own.js';
import { newErrorViolations, describeCounterexample } from './integrity.js';
import { attachExtracted, attachObserved, extractedChange, stripExtracted, derivedEvidenceDiagnostics } from './extraction.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {import('./types.js').Operation} Operation */
/** @typedef {import('./types.js').TransactionResult} TransactionResult */
/** @typedef {ReturnType<typeof analyzeSpec>|ReturnType<typeof analyzeLayers>} Analysis */

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
   * @param {{specText: string, layoutText?: string|null, name?: string, layers?: import('./layers.js').ProductLayer[], extracted?: import('./extraction.js').ExtractedFacts|null, observed?: import('./extraction.js').ObservedFacts|null}} init
   *   extracted and observed are facts read from outside (src/core/extraction.js); they become relationships of the model,
   *   with their own provenance, and are replaced as a whole by setFacts
   */
  constructor(init) {
    this.name = init.name ?? '';
    this.specText = init.specText;
    /** The product files layered on the specification, in order (none for most projects). */
    this.layers = init.layers ?? [];
    /** The extracted facts (static imports of the implementation surface) the model carries, or null. */
    this.extracted = init.extracted ?? null;
    /** The observed facts (a recording's events) the model carries, or null. */
    this.observed = init.observed ?? null;
    /** @type {Model|null} the model of the platform text alone; the model itself when there are no layers */
    this.baseModel = null;
    /** The semantic hash of the combined model; equal to semanticHash when there are no layers. */
    this.layeredHash = '';
    /** @type {{file: string, product: string|null, entities: string[]}[]} what each product file declares */
    this.layerSummary = [];
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
   * @param {Analysis} [analysis] the analysis of exactly this.specText, when the caller already has it
   */
  #derive(analysis) {
    const a = analysis ?? this.#analyze(this.specText);
    this.model = this.#withFacts(a.model);
    this.#analysisDiagnostics = { diagnostics: a.diagnostics, errorCount: a.errorCount };
    this.#factDiagnostics();
    if ('baseHash' in a) {
      this.baseModel = a.baseModel;
      this.semanticHash = a.baseHash;
      this.layeredHash = a.layeredHash;
      this.layerSummary = a.layers;
    } else {
      this.layerSummary = [];
      this.baseModel = a.model;
      this.semanticHash = semanticHash(a.model);
      this.layeredHash = this.semanticHash;
    }
    this.layout = parseLayout(this.layoutText);
  }

  /** The diagnostics of the analysis of the specification text, before the facts' are added. */
  #analysisDiagnostics = { diagnostics: /** @type {Diagnostic[]} */ ([]), errorCount: 0 };

  /** The analysis's diagnostics followed by those of the evidence the facts derive from tests (WG-5705). */
  #factDiagnostics() {
    const extra = derivedEvidenceDiagnostics(this.model);
    this.diagnostics = extra.length ? [...this.#analysisDiagnostics.diagnostics, ...extra] : this.#analysisDiagnostics.diagnostics;
    this.errorCount = this.#analysisDiagnostics.errorCount + extra.filter((d) => d.severity === 'error').length;
  }

  /** The model with this project's extracted and observed facts attached. @param {Model|null} model */
  #withFacts(model) {
    if (!model) return model;
    return attachObserved(attachExtracted(model, this.extracted), this.observed);
  }

  /**
   * Replace the extracted and/or observed facts (an implementation change, a new recording). The specification is
   * untouched. The result lists the relationship ids whose facts changed: the `affected` set to give rederive and
   * claimsToRecompute, so the change propagates through footprints like an edit.
   * @param {{extracted?: import('./extraction.js').ExtractedFacts|null, observed?: import('./extraction.js').ObservedFacts|null}} facts
   * @returns {{before: Model|null, after: Model|null, affected: string[]}}
   */
  setFacts(facts) {
    const before = this.model;
    if (facts.extracted !== undefined) this.extracted = facts.extracted;
    if (facts.observed !== undefined) this.observed = facts.observed;
    this.model = this.#withFacts(before ? stripExtracted(before) : before);
    this.#factDiagnostics();
    return { before, after: this.model, affected: before && this.model ? extractedChange(before, this.model) : [] };
  }

  /**
   * The analysis of a specification text, with the product files layered on it when there are any
   * (this project's, unless the caller gives the ones it is about to adopt).
   * @param {string} text @param {import('./layers.js').ProductLayer[]} [layers] @returns {Analysis}
   */
  #analyze(text, layers = this.layers) {
    return layers.length ? analyzeLayers(text, layers) : analyzeSpec(text);
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
   * @param {{label?: string, origin?: string, expectRevision?: number, expectHash?: string, perOperation?: boolean}} [opts]
   *   expectRevision / expectHash: optimistic concurrency. The transaction is
   *   refused with code "revision.stale" when the project has moved on.
   *   perOperation: re-derive the model after every edit, the reference behaviour that the
   *   batched transaction is tested against; the result is the same, only slower.
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
    if (this.layers.length) {
      for (const op of list) {
        const id = typeof op.id === 'string' ? op.id : null;
        const e = id !== null ? this.model?.entities.get(id) : undefined;
        if (e?.loc.file !== undefined) return this.#fail('layer.product-entity', `"${id}" is declared by product file ${e.loc.file}; transactions edit only the platform specification, so edit that file instead.`);
      }
    }
    // Operations act on the platform text, so they read the platform's own model (the same as the model without layers).
    // The operations run on one transaction that re-derives the model only when an operation needs
    // it and once at the end (operations.js, Tx). Should its index of declarations turn out not to
    // match a model it derived, the transaction is replayed re-deriving after every edit.
    /** @param {boolean} eager */
    const run = (eager) => {
      const tx = new Tx(this.specText, this.layoutText, /** @type {Model} */ (this.baseModel ?? this.model), { eager, diagnostics: this.diagnostics });
      try {
        for (const op of list) OPERATIONS[op.type].apply(tx, op);
        return { tx, parsed: tx.specEdited ? tx.parsed() : null, error: null };
      } catch (e) {
        if (!(e instanceof OpError)) throw e;
        tx.check();
        return { tx, parsed: null, error: e };
      }
    };
    let r = run(opts.perOperation === true);
    if (r.tx.diverged) r = run(true);
    if (r.error) return this.#fail(r.error.code, r.error.message, r.error.diagnostics);
    const tx = r.tx;
    /** @type {Analysis|undefined} */
    let analysis;
    if (tx.specEdited) {
      // With product layers the result is analysed with them; without, from the text the transaction already parsed.
      analysis = this.layers.length ? this.#analyze(tx.specText) : analyzeSpec(tx.specText, r.parsed);
      if (analysis.errorCount || !analysis.model) {
        return this.#fail('validation.failed', `Rejected: the result would have ${analysis.errorCount} validation error(s).`, analysis.diagnostics.filter((d) => d.severity === 'error' && d.code !== 'integrity.violated'));
      }
      const added = newErrorViolations(this.model, analysis.model);
      if (added.length) {
        const after = /** @type {Model} */ (analysis.model);
        /** @type {Diagnostic[]} */
        const diagnostics = added.map(({ ruleId, statement, counterexample }) => {
          const key = counterexample.values.find((k) => k.startsWith('s:') && after.entities.has(k.slice(2)));
          const at = /** @type {any} */ (after.entities.get(key ? key.slice(2) : ruleId));
          return { code: 'integrity.violated', severity: 'error', message: `Integrity rule "${ruleId}" would be violated: ${describeCounterexample(after, counterexample)}. ${statement}`, entityId: at.id, loc: at.loc, path: at.path };
        });
        return this.#fail('integrity.violated', `Rejected: the result would add ${added.length} violation(s) of integrity rules (${[...new Set(added.map((a) => a.ruleId))].join(', ')}).`, diagnostics);
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
   * @param {Analysis} [analysis] analysis of `specText`, when already computed
   * @param {boolean} [layersChanged] the product files changed: the model is derived again though the text is the same
   * @returns {TransactionResult}
   */
  #commit(specText, layoutText, meta, recordUndo, analysis, layersChanged = false) {
    const before = { specText: this.specText, layoutText: this.layoutText };
    const hashBefore = this.semanticHash;
    const specChanged = specText !== this.specText || layersChanged;
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
   * `layers` is the product files as they are on disk now (all of them, as the constructor takes
   * them); when they differ from the ones held, the layered model is derived from the new ones.
   * @param {{specText?: string, layoutText?: string, layers?: import('./layers.js').ProductLayer[]}} texts
   * @returns {TransactionResult}
   */
  reload(texts) {
    const specText = texts.specText ?? this.specText;
    const layoutText = texts.layoutText ?? this.layoutText;
    const layers = texts.layers ?? this.layers;
    const layersChanged = JSON.stringify(layers) !== JSON.stringify(this.layers);
    if (specText === this.specText && layoutText === this.layoutText && !layersChanged) {
      return { ok: true, diagnostics: this.diagnostics, revision: this.revision, semanticHash: this.semanticHash, affected: [], semanticChanged: false };
    }
    const analysis = specText !== this.specText || layersChanged ? this.#analyze(specText, layers) : undefined;
    if (analysis && !analysis.model) return this.#fail('reload.syntax', 'The file on disk has syntax errors; the last valid model is kept.', analysis.diagnostics);
    const usableLayout = parseLayout(layoutText).ok ? layoutText : this.layoutText;
    const beforeData = new Map(this.model ? [...this.model.entities].map(([id, e]) => [id, JSON.stringify(e.data)]) : []);
    const after = (analysis ?? this.#analyze(specText, layers)).model;
    const affected = [];
    if (after) {
      for (const [id, e] of after.entities) if (beforeData.get(id) !== JSON.stringify(e.data)) affected.push(id);
      for (const id of beforeData.keys()) if (!after.entities.has(id)) affected.push(id);
    }
    // The reload is not undoable: undoing would write pre-reload text over the newer file on disk.
    this.undoStack.length = 0;
    this.redoStack.length = 0;
    this.layers = layers;
    return this.#commit(specText, usableLayout, { label: 'Reloaded from disk', origin: 'external', ops: ['Reload'], affected }, false, analysis, layersChanged);
  }
}
