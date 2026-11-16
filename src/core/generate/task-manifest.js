// tasks.json: the agent-consumable list of what is still to be done, derived from
// the model, its claim results, its diagnostics and the source traceability check.

import { entityLabel } from '../query.js';
import { semanticHash } from '../hash.js';
import { oneLine, list, nameOf, sourceOf, json } from './manifest.js';
import { claimRows } from './claims-report.js';

/** @typedef {import('../types.js').Model} Model */
/** @typedef {import('../types.js').Entity} Entity */
/** @typedef {import('../types.js').Diagnostic} Diagnostic */
/** @typedef {import('../claims.js').ClaimResult} ClaimResult */

/**
 * @typedef {Object} Task
 * @property {string} id
 * @property {string} type
 * @property {'high'|'medium'|'low'} severity
 * @property {string} title
 * @property {string} detail
 * @property {string[]} entities
 * @property {{line: number, column: number}|null} source
 */

/** Task types in output order. Tasks are grouped by type in this order, then by declaration order. */
const TYPE_ORDER = [
  'violated-claim', 'validation', 'not-implemented', 'traceability',
  'inconclusive-claim', 'unevaluated-claim', 'undeclared-realisation', 'unknown', 'gap',
];

/** @param {any[]} xs */
const unique = (xs) => [...new Set(xs.filter((x) => typeof x === 'string'))];

/**
 * @param {Model} model
 * @param {{claimResults?: ClaimResult[], diagnostics?: Diagnostic[], traceability?: {missingModules?: {component: string, module: string}[], unclaimedFiles?: string[]}}} [opts]
 * @returns {string} tasks.json text
 */
export function generateTaskManifest(model, opts = {}) {
  /** @type {Task[]} */
  const tasks = [];
  const rows = claimRows(model, opts.claimResults ?? []);
  const diagnostics = opts.diagnostics ?? [];
  const traceability = opts.traceability ?? { checkedModules: 0, missingModules: [], unclaimedFiles: [] };

  /** @type {Set<string>} */
  const usedIds = new Set();
  /** @param {Diagnostic} d */
  const diagId = (d) => {
    const base = `diag:${d.code}:${d.entityId ?? 'model'}`;
    let id = base;
    let n = 1;
    while (usedIds.has(id)) { n++; id = `${base}:${n}`; }
    usedIds.add(id);
    return id;
  };
  /** @param {Diagnostic} d */
  const diagSource = (d) => {
    const e = d.entityId ? model.entities.get(d.entityId) : undefined;
    if (e) return sourceOf(e);
    return d.loc ? { line: d.loc.line, column: d.loc.column } : null;
  };

  // 1. violated claims
  for (const { claim, result } of rows) {
    if (result.status !== 'violated') continue;
    const ce = result.counterexample;
    tasks.push({
      id: `claim:${claim.id}:violated`,
      type: 'violated-claim',
      severity: 'high',
      title: `Claim "${oneLine(claim.id)}" is violated`,
      detail: [oneLine(result.explanation), ce ? oneLine(ce.summary) : ''].filter(Boolean).join(' '),
      entities: unique([claim.id, ...(ce?.entities ?? [])]),
      source: sourceOf(claim),
    });
  }

  // 2. validation warnings
  for (const d of diagnostics) {
    if (d.severity !== 'warning') continue;
    tasks.push({
      id: diagId(d),
      type: 'validation',
      severity: 'medium',
      title: oneLine(d.message),
      detail: `Validation warning ${oneLine(d.code)}.`,
      entities: d.entityId ? [d.entityId] : [],
      source: diagSource(d),
    });
  }

  // 3. components declared not-implemented
  for (const c of model.byKind.component ?? []) {
    if (c.data.implementation?.status !== 'not-implemented') continue;
    const modules = list(c.data.implementation.modules).map((m) => oneLine(m));
    const detail = [modules.length ? `Modules: ${modules.join(', ')}.` : 'No modules are declared.', c.data.implementation.notes ? oneLine(c.data.implementation.notes) : '']
      .filter(Boolean).join(' ');
    tasks.push({
      id: `impl:${c.id}:not-implemented`,
      type: 'not-implemented',
      severity: 'high',
      title: `Component "${oneLine(entityLabel(c))}" is declared not-implemented`,
      detail,
      entities: [c.id],
      source: sourceOf(c),
    });
  }

  // 4. traceability: declared modules that are missing, then source files no component claims
  for (const m of traceability.missingModules ?? []) {
    tasks.push({
      id: `trace:missing:${m.component}:${m.module}`,
      type: 'traceability',
      severity: 'medium',
      title: `Module declared by ${oneLine(m.component)} does not exist: ${oneLine(m.module)}`,
      detail: `${nameOf(model, m.component)} lists this module in implementation.modules, but no such file was found.`,
      entities: [m.component],
      source: sourceOf(model.entities.get(m.component)),
    });
  }
  for (const f of traceability.unclaimedFiles ?? []) {
    tasks.push({
      id: `trace:unclaimed:${f}`,
      type: 'traceability',
      severity: 'medium',
      title: `Source file is not claimed by any component: ${oneLine(f)}`,
      detail: 'No component lists this file in implementation.modules.',
      entities: [],
      source: null,
    });
  }

  // 5. inconclusive claims, then claims not evaluated
  for (const { claim, result } of rows) {
    if (result.status !== 'inconclusive') continue;
    tasks.push({
      id: `claim:${claim.id}:inconclusive`,
      type: 'inconclusive-claim',
      severity: 'medium',
      title: `Claim "${oneLine(claim.id)}" is inconclusive`,
      detail: oneLine(result.explanation),
      entities: unique([claim.id, ...(result.involved ?? [])]),
      source: sourceOf(claim),
    });
  }
  for (const { claim, result } of rows) {
    if (result.status !== 'not-evaluated') continue;
    tasks.push({
      id: `claim:${claim.id}:not-evaluated`,
      type: 'unevaluated-claim',
      severity: 'low',
      title: `Claim "${oneLine(claim.id)}" is not evaluated`,
      detail: oneLine(result.explanation),
      entities: unique([claim.id, ...(result.involved ?? [])]),
      source: sourceOf(claim),
    });
  }

  // 6. components without a realisation, only once the model declares realisations at all
  const components = model.byKind.component ?? [];
  if (components.some((c) => c.data.implementation !== undefined)) {
    for (const c of components) {
      if ((c.data.kind ?? 'component') === 'subsystem' || c.data.implementation !== undefined) continue;
      tasks.push({
        id: `impl:${c.id}:undeclared`,
        type: 'undeclared-realisation',
        severity: 'low',
        title: `Component "${oneLine(entityLabel(c))}" declares no realisation`,
        detail: 'Its implementation status is unknown until it declares implementation.status.',
        entities: [c.id],
        source: sourceOf(c),
      });
    }
  }

  // 7. known unknowns
  for (const c of components) {
    list(c.data.unknowns).forEach((u, i) => {
      tasks.push({
        id: `unknown:${c.id}:${i}`,
        type: 'unknown',
        severity: 'low',
        title: oneLine(u),
        detail: `Known unknown of ${oneLine(entityLabel(c))}.`,
        entities: [c.id],
        source: sourceOf(c),
      });
    });
  }

  // 8. specification gaps (info diagnostics)
  for (const d of diagnostics) {
    if (d.severity !== 'info') continue;
    tasks.push({
      id: diagId(d),
      type: 'gap',
      severity: 'low',
      title: oneLine(d.message),
      detail: `Specification gap ${oneLine(d.code)}.`,
      entities: d.entityId ? [d.entityId] : [],
      source: diagSource(d),
    });
  }

  // The tasks array is built group by group above, so it is already in the output order.
  const byType = /** @type {Record<string, number>} */ ({});
  for (const type of TYPE_ORDER) byType[type] = tasks.filter((t) => t.type === type).length;

  return json({
    format: 'exegra-tasks',
    version: 1,
    semanticHash: semanticHash(model),
    summary: { total: tasks.length, byType },
    tasks,
  });
}
