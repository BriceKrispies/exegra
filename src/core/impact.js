// Change impact: the dependency graph of a specification's claims and the claims a change re-marks
// (WG-5684, criteria 7 to 10). The graph is built here from the model and the recorded facts; which claims a
// change re-marks is decided in Lean (formal/Exegra/Impact.lean, `impacted`).
//
// Nodes: claim, assumption, specEntity, leanDecl, file, measurement, evidence. Edges (a depends on b):
//   claim -> each assumption it cites; assumption -> each claim that discharges it (`discharges`);
//   claim -> each specification entity its `evaluate` names;
//   claim -> each of its evidence entities; test evidence -> its test file and the files the run of its test
//     covered (recorded by verify as `covers`, from the runner's coverage of that test);
//   measurement evidence -> a measurement node -> its file;
//   lean-theorem claim -> its theorem -> the declarations its statement uses and the files defining them (as the
//     recorded theorem check reports them: `file` and `declarations`).
// A change set names the files it touches and the transaction operations it applies to the specification; the
// entities those operations add, change or remove are its changed specification nodes.

import { call } from './lean.js';
import { stableStringify } from './stable-json.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {'claim'|'assumption'|'specEntity'|'leanDecl'|'file'|'measurement'|'evidence'} NodeKind */
/** @typedef {{kind: NodeKind, id: string}} ImpactNode */
/** @typedef {{edges: [ImpactNode, ImpactNode][], claims: string[]}} ImpactGraph */
/**
 * @typedef {{claim: string, change: 'statement'|'evaluate'|'removed'|'added'|'theorem-statement', before?: any, after?: any}} GuaranteeChange
 *   a change of what a claim guarantees: its statement, its evaluate, its theorem's statement hash; or the claim
 *   removed or added
 */

/** The node of a specification entity. @param {any} e @returns {ImpactNode} */
function entityNode(e) {
  const kind = e.kind === 'claim' ? 'claim' : e.kind === 'assumption' ? 'assumption' : e.kind === 'evidence' ? 'evidence' : 'specEntity';
  return { kind, id: e.id };
}

/** The file of a test reference (before its `#pattern`). @param {string} ref */
export const refFile = (ref) => {
  const at = ref.indexOf('#');
  return (at < 0 ? ref : ref.slice(0, at)).trim().replace(/\\/g, '/');
};

/** Every string inside a value. @param {any} v @param {string[]} out */
function strings(v, out = []) {
  if (typeof v === 'string') out.push(v);
  else if (Array.isArray(v)) for (const x of v) strings(x, out);
  else if (v && typeof v === 'object') for (const x of Object.values(v)) strings(x, out);
  return out;
}

/**
 * The dependency graph of a model's claims.
 * @param {Model} model
 * @param {{recorded?: any}} [opts] recorded: the results file (evidence `covers`, theorem `file` and `declarations`)
 * @returns {ImpactGraph}
 */
export function dependencyGraph(model, opts = {}) {
  const recorded = opts.recorded ?? {};
  /** @type {[ImpactNode, ImpactNode][]} */
  const edges = [];
  const seen = new Set();
  /** @param {ImpactNode} a @param {ImpactNode} b */
  const edge = (a, b) => {
    const key = `${a.kind}\0${a.id}\0${b.kind}\0${b.id}`;
    if (seen.has(key)) return;
    seen.add(key);
    edges.push([a, b]);
  };
  const claims = model.byKind.claim ?? [];
  for (const c of claims) {
    const node = /** @type {ImpactNode} */ ({ kind: 'claim', id: c.id });
    for (const a of Array.isArray(c.data.assumptions) ? c.data.assumptions : []) if (typeof a === 'string') edge(node, { kind: 'assumption', id: a });
    for (const a of Array.isArray(c.data.discharges) ? c.data.discharges : []) if (typeof a === 'string') edge({ kind: 'assumption', id: a }, node);
    const ev = c.data.evaluate && typeof c.data.evaluate === 'object' ? c.data.evaluate : null;
    if (ev) {
      for (const s of strings(ev)) {
        const e = model.entities.get(s);
        if (e && e.id !== c.id) edge(node, entityNode(e));
      }
      if (ev.method === 'lean-theorem' && typeof ev.theorem === 'string' && ev.theorem) {
        const thm = /** @type {ImpactNode} */ ({ kind: 'leanDecl', id: ev.theorem });
        edge(node, thm);
        const rec = recorded.theorems && Object.hasOwn(recorded.theorems, ev.theorem) ? recorded.theorems[ev.theorem] : null;
        if (rec && typeof rec.file === 'string' && rec.file) edge(thm, { kind: 'file', id: rec.file });
        for (const d of Array.isArray(rec?.declarations) ? rec.declarations : []) {
          if (!d || typeof d.name !== 'string') continue;
          const decl = /** @type {ImpactNode} */ ({ kind: 'leanDecl', id: d.name });
          if (d.name !== ev.theorem) edge(thm, decl);
          if (typeof d.file === 'string' && d.file) edge(decl, { kind: 'file', id: d.file });
        }
      }
    }
  }
  for (const e of model.byKind.evidence ?? []) {
    if (typeof e.data.claim !== 'string') continue;
    const node = /** @type {ImpactNode} */ ({ kind: 'evidence', id: e.id });
    edge({ kind: 'claim', id: e.data.claim }, node);
    const ref = typeof e.data.ref === 'string' ? e.data.ref : '';
    if (e.data.kind === 'test' && ref) {
      edge(node, { kind: 'file', id: refFile(ref) });
      const rec = recorded.results && Object.hasOwn(recorded.results, e.id) ? recorded.results[e.id] : null;
      for (const f of Array.isArray(rec?.covers) ? rec.covers : []) if (typeof f === 'string') edge(node, { kind: 'file', id: f });
    } else if (e.data.kind === 'measurement' && ref) {
      const m = /** @type {ImpactNode} */ ({ kind: 'measurement', id: e.id });
      edge(node, m);
      edge(m, { kind: 'file', id: refFile(ref) });
    }
  }
  return { edges, claims: claims.map((c) => c.id) };
}

/**
 * What a change does to the specification: the entities it adds, changes or removes (as nodes), and the changes
 * of guarantees among them (a claim's statement or evaluate changed, a claim added or removed).
 * @param {Model} before @param {Model} after
 * @returns {{nodes: ImpactNode[], guaranteeChanges: GuaranteeChange[]}}
 */
export function specChanges(before, after) {
  /** @type {ImpactNode[]} */
  const nodes = [];
  /** @type {GuaranteeChange[]} */
  const guaranteeChanges = [];
  const ids = [...new Set([...before.entities.keys(), ...after.entities.keys()])].sort();
  for (const id of ids) {
    const b = before.entities.get(id);
    const a = after.entities.get(id);
    if (b && a && b.kind === a.kind && stableStringify(b.data) === stableStringify(a.data)) continue;
    const e = /** @type {any} */ (a ?? b);
    nodes.push(entityNode(e));
    if (e.kind !== 'claim') continue;
    if (!a) guaranteeChanges.push({ claim: id, change: 'removed', before: claimShown(b) });
    else if (!b) guaranteeChanges.push({ claim: id, change: 'added', after: claimShown(a) });
    else {
      if (b.data.statement !== a.data.statement) guaranteeChanges.push({ claim: id, change: 'statement', before: b.data.statement, after: a.data.statement });
      if (stableStringify(b.data.evaluate ?? null) !== stableStringify(a.data.evaluate ?? null)) guaranteeChanges.push({ claim: id, change: 'evaluate', before: b.data.evaluate ?? null, after: a.data.evaluate ?? null });
    }
  }
  return { nodes, guaranteeChanges };
}

/** @param {any} e */
const claimShown = (e) => ({ statement: e?.data?.statement, evaluate: e?.data?.evaluate ?? null });

/**
 * The claims a change re-marks, decided in Lean (Exegra.Impact.impacted): those from which a changed node is
 * reachable in the graph, a changed claim included.
 * @param {ImpactGraph} graph @param {ImpactNode[]} changed
 * @returns {string[]}
 */
export function impactedClaims(graph, changed) {
  if (!changed.length || !graph.claims.length) return [];
  const r = call('impact.claims', { edges: graph.edges, claims: graph.claims, changed });
  if (!r.ok) throw new Error(`The Lean change impact could not be computed: ${r.error}`);
  return r.value;
}

/**
 * The file nodes of a change set's files, repository-relative with forward slashes.
 * @param {string[]} files @returns {ImpactNode[]}
 */
export function fileNodes(files) {
  return files.map((f) => ({ kind: /** @type {const} */ ('file'), id: f.replace(/\\/g, '/').replace(/^\.\//, '') }));
}

/**
 * The impact of a change: the claims to re-mark, and which of them change a guarantee.
 * @param {Model} before the specification before the change @param {Model} after the specification after it
 * @param {{files?: string[], recorded?: any}} [opts] files: the files the change touches (Lean sources, tests,
 *   measurements); recorded: the results file of the last verification
 * @returns {{remark: string[], guaranteeChanges: GuaranteeChange[], changed: ImpactNode[]}}
 */
export function changeImpact(before, after, opts = {}) {
  const spec = specChanges(before, after);
  const changed = [...spec.nodes, ...fileNodes(opts.files ?? [])];
  // Claims of either side: a removed claim is re-marked (it is gone), an added one is marked for the first time.
  const graphAfter = dependencyGraph(after, { recorded: opts.recorded });
  const graphBefore = dependencyGraph(before, { recorded: opts.recorded });
  const remark = [...new Set([...impactedClaims(graphBefore, changed), ...impactedClaims(graphAfter, changed)])].sort();
  return { remark, guaranteeChanges: spec.guaranteeChanges, changed };
}
