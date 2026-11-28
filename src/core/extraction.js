// Extracted and observed facts in the model (WG-5696, M5). Pure and browser-safe: it reads facts as data and never
// touches the file system. The facts come from outside:
//
//   extracted   tools/extract.js reads the implementation surface and writes a fact file (specs/<project>/extracted/
//               facts.json): per file its digest and its imports. Static structure only.
//   observed    tools/observe.js reads a recorded session (the traffic recorder's stream) and writes a fact file of
//               how often each event of the specification occurred, naming the recording.
//
// Both enter the model as relationships with their own provenance (interactions.js), kept beside the declared ones and
// never merged into them (invariant I2): `attachExtracted` returns a model whose relationships are the declared ones
// followed by one `imports` relationship per ordered pair of module elements the extracted imports connect (provenance
// `extracted`, the file edges it stands for in `sources`). Everything downstream, the derived model at every cut
// (abstraction.js), the graph claims (claims.js) and their footprints (footprints.js), reads those relationships like any
// other, so an extracted import is a witness at the module, component, subsystem and system cuts. A change of the facts
// is a change of those relationships (`extractedChange`), and goes through the same footprints as an edit.
//
// Inside the extraction surface a static dependency is derived from the code, not declared. `reconcile` reports where
// the declarations and the facts disagree. Runtime wiring (invokes, notifies, composes, ...) stays declared: it is
// never flagged merely for being unextracted, and a declared runtime interaction no recording shows is "not observed",
// never "false".

import { moduleDeclarations, elementsOf, componentOf, claimSubjects } from './query.js';
import { CLAIM_METHODS } from './claim-methods.js';
import { sha256Hex } from './sha256.js';
import { kindInfo, provenanceOf } from './interactions.js';
import { eventExchange, eventsBetween } from './abstraction.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

export const FACTS_FORMAT = 'exegra-extracted-facts/1';
export const OBSERVED_FORMAT = 'exegra-observed-facts/1';
/** Id prefixes of the relationships the facts become. */
export const EXTRACTED_PREFIX = 'extracted:';
/** Id prefix of the evidence entities derived from the claim markers of tests (WG-5705). */
export const DERIVED_EVIDENCE_PREFIX = 'extracted:evidence:';
export const OBSERVED_PREFIX = 'observed:';

/** The scope sentence every result that rests on extracted relationships carries. */
export const STATIC_ONLY = 'Extracted relationships are static imports only: they say which files name which, never that the code runs that way.';

/** Extracted and observed relationships have no place in the specification text. */
const NO_LOC = { offset: 0, length: 0, line: 0, column: 0 };

const byText = (/** @type {string} */ a, /** @type {string} */ b) => (a < b ? -1 : a > b ? 1 : 0);

/**
 * @typedef {{spec: string, how: string, resolved: string|null, external: boolean}} ImportFact
 * @typedef {{path: string, language: string, digest: string, imports: ImportFact[]}} FileFact
 * @typedef {{claim: string, ref: string, file: string, line: number}} EvidenceFact
 *   a test's claim marker (tools/extract.js, testEvidence): the test `ref` evidences `claim`
 * @typedef {{file: string, line: number, message: string}} EvidenceProblem
 * @typedef {{format: string, provenance: 'extracted', extractor: {id: string, version: string}, files: FileFact[], evidence?: EvidenceFact[], evidenceProblems?: EvidenceProblem[]}} ExtractedFacts
 * @typedef {{format: string, provenance: 'observed', recording: {id: string, source?: string, digest?: string, events: number}, events: Record<string, number>}} ObservedFacts
 * @typedef {{id: string, from: string, to: string, fromPath: string, toPath: string, sources: {from: string, to: string, how: string}[], dynamic: boolean}} ExtractedEdge
 * @typedef {{facts: ExtractedFacts, edges: ExtractedEdge[], external: {from: string, spec: string, how: string}[], unowned: string[], notExtracted: {component: string, path: string}[], relationshipIds: string[], evidenceIds?: string[]}} Extraction
 */

/**
 * Problems with a fact file's shape, as messages; empty when it can be read.
 * @param {any} facts @returns {string[]}
 */
export function checkFacts(facts) {
  /** @type {string[]} */
  const out = [];
  if (!facts || typeof facts !== 'object') return ['the fact file is not an object'];
  if (facts.format !== FACTS_FORMAT) out.push(`format is ${JSON.stringify(facts.format)}, not "${FACTS_FORMAT}"`);
  if (facts.provenance !== 'extracted') out.push('provenance is not "extracted"');
  if (!facts.extractor || typeof facts.extractor.id !== 'string' || typeof facts.extractor.version !== 'string') out.push('the extractor identity and version are missing');
  if (!Array.isArray(facts.files)) { out.push('files is not a list'); return out; }
  if (facts.evidence !== undefined && (!Array.isArray(facts.evidence) || !facts.evidence.every((/** @type {any} */ e) => e && typeof e.claim === 'string' && typeof e.ref === 'string' && typeof e.file === 'string'))) out.push('evidence is not a list of {claim, ref, file, line}');
  const seen = new Set();
  for (const f of facts.files) {
    if (!f || typeof f.path !== 'string' || typeof f.digest !== 'string' || !Array.isArray(f.imports)) { out.push(`a file entry lacks a path, a digest or imports: ${JSON.stringify(f)?.slice(0, 80)}`); continue; }
    if (seen.has(f.path)) out.push(`${f.path} is listed twice`);
    seen.add(f.path);
  }
  return out;
}

/**
 * Module declarations of the model, each with the file it covers decided by specificity: a file entry over a
 * directory, a deeper directory over a shallower, the first declared on a tie. The owner of a file.
 * @param {Model} model @returns {(file: string) => ReturnType<typeof moduleDeclarations>[number]|null}
 */
function ownerFinder(model) {
  const decls = moduleDeclarations(model);
  /** @type {Map<string, ReturnType<typeof moduleDeclarations>[number]|null>} */
  const memo = new Map();
  return (file) => {
    if (memo.has(file)) return /** @type {any} */ (memo.get(file));
    /** @type {ReturnType<typeof moduleDeclarations>[number]|null} */
    let best = null;
    let len = -1;
    for (const d of decls) {
      const dir = d.path.endsWith('/');
      if (!(dir ? file.startsWith(d.path) : file === d.path)) continue;
      const l = dir ? d.path.length : Infinity;
      if (l > len) { best = d; len = l; }
    }
    memo.set(file, best);
    return best;
  };
}

/**
 * The relationships the extracted facts stand for, lifted to the module elements that own the files: one `imports`
 * relationship per ordered pair of distinct module elements. Imports within one module element are internal to it
 * and give none. A specifier that names no file of the surface (a package, a builtin) is listed in `external`.
 * @param {Model} model @param {ExtractedFacts} facts
 * @returns {Extraction}
 */
export function liftExtracted(model, facts) {
  const owner = ownerFinder(model);
  /** @type {Map<string, ExtractedEdge>} */
  const edges = new Map();
  /** @type {Extraction['external']} */
  const external = [];
  /** @type {Set<string>} */
  const unowned = new Set();
  const covered = new Set();
  const inFacts = new Set(facts.files.map((f) => f.path));
  for (const f of facts.files) {
    const from = owner(f.path);
    if (from) covered.add(`${from.component}\0${from.path}`);
    else unowned.add(f.path);
    for (const i of f.imports) {
      if (i.resolved === null) { if (i.external) external.push({ from: f.path, spec: i.spec, how: i.how }); continue; }
      const to = owner(i.resolved);
      if (!from || !to) { if (!to && inFacts.has(i.resolved)) unowned.add(i.resolved); continue; }
      if (from.id === to.id) continue;
      const key = `${from.id}\0${to.id}`;
      let e = edges.get(key);
      if (!e) {
        e = { id: `${EXTRACTED_PREFIX}imports:${from.path}=>${to.path}`, from: from.id, to: to.id, fromPath: from.path, toPath: to.path, sources: [], dynamic: true };
        edges.set(key, e);
      }
      e.sources.push({ from: f.path, to: i.resolved, how: i.how });
      if (i.how !== 'dynamic') e.dynamic = false;
    }
  }
  const list = [...edges.values()].sort((a, b) => byText(a.id, b.id));
  const notExtracted = moduleDeclarations(model).filter((d) => !covered.has(`${d.component}\0${d.path}`)).map((d) => ({ component: d.component, path: d.path }));
  return { facts, edges: list, external, unowned: [...unowned].sort(byText), notExtracted, relationshipIds: list.map((e) => e.id) };
}

/** The relationship entity an extracted edge becomes. @param {ExtractedEdge} e @param {ExtractedFacts} facts @returns {Entity} */
function edgeEntity(e, facts) {
  return /** @type {Entity} */ (/** @type {unknown} */ ({
    id: e.id, kind: 'relationship', owner: null, path: [e.id], loc: NO_LOC,
    data: {
      id: e.id, kind: 'imports', from: e.from, to: e.to, provenance: 'extracted', dynamic: e.dynamic,
      description: `Extracted: ${e.sources.length} static ${e.sources.length === 1 ? 'import' : 'imports'} from ${e.fromPath} to ${e.toPath} (${e.sources.map((s) => `${s.from} -> ${s.to}`).slice(0, 3).join('; ')}${e.sources.length > 3 ? '; ...' : ''}).`,
      extractor: facts.extractor, sources: e.sources,
    },
  }));
}

// ---------------------------------------------------------------------------------------------
// Evidence derived from tests (WG-5705)
//
// A test names the claims it evidences with a marker comment (tools/extract.js reads it, docs/claims-and-evidence.md):
//
//   // @evidence claim-a claim-b               directly above a test with a literal title: the reference file#title
//   // @evidence claim-a # <title pattern>     anywhere in the file: the reference file#pattern (generated titles)
//   // @evidence claim-a #                     anywhere in the file: the whole file
//
// The extractor records each (claim, reference) in the fact file; they enter the model as evidence entities of kind
// test, after the declared ones, exactly as a declared test evidence would. Declared evidence stays for what a test
// cannot carry: measurements, reviews, documents and contradicting evidence (supports: false).

const SEP = String.fromCharCode(0);

/** The id of the evidence entity a test's marker derives for a claim and a reference. @param {string} claim @param {string} ref */
export function derivedEvidenceId(claim, ref) {
  return `${DERIVED_EVIDENCE_PREFIX}${claim}:${sha256Hex(`${claim}${SEP}${ref}`).slice(0, 12)}`;
}

/**
 * The evidence entities the facts' test markers derive, one per distinct (claim, reference), in the facts' order.
 * @param {ExtractedFacts} facts @returns {Entity[]}
 */
export function derivedEvidence(facts) {
  /** @type {Map<string, Entity>} */
  const out = new Map();
  for (const e of facts.evidence ?? []) {
    const id = derivedEvidenceId(e.claim, e.ref);
    if (out.has(id)) continue;
    out.set(id, /** @type {Entity} */ (/** @type {unknown} */ ({
      id, kind: 'evidence', owner: null, path: [id], loc: NO_LOC,
      data: { id, claim: e.claim, kind: 'test', ref: e.ref, provenance: 'extracted', source: { file: e.file, line: e.line } },
    })));
  }
  return [...out.values()];
}

/** Whether an evidence entity was derived from a test's marker. @param {Entity|{id: string}} e */
export const isDerivedEvidence = (e) => e.id.startsWith(DERIVED_EVIDENCE_PREFIX);

/**
 * Diagnostics of the evidence derived from tests (WG-5705): a marker that names no claim of the model, a marker the
 * extractor could not read, and a declared test evidence that says what a test's marker already derives (the
 * declaration is redundant and must go; declared evidence is for what a test cannot carry).
 * @param {Model|null} model
 * @returns {import('./types.js').Diagnostic[]}
 */
export function derivedEvidenceDiagnostics(model) {
  const x = model ? extractionOf(model) : null;
  if (!model || !x) return [];
  /** @type {any[]} */
  const out = [];
  const derived = (model.byKind.evidence ?? []).filter(isDerivedEvidence);
  const derivedKeys = new Set(derived.map((e) => `${e.data.claim}${SEP}${e.data.ref}`));
  /** @type {Set<string>} */
  const unnamed = new Set();
  for (const e of derived) {
    const c = model.entities.get(e.data.claim);
    if (!c || c.kind !== 'claim') {
      out.push({ code: 'evidence.marker-unknown-claim', severity: 'error', entityId: e.id, path: ['claim'],
        message: `${e.data.source?.file}:${e.data.source?.line}: the test marker names "${e.data.claim}", which is not a claim of the specification.` });
    } else if (!unnamed.has(c.id) && !claimSubjects(model, c, CLAIM_METHODS[c.data.evaluate?.method]?.params).length) {
      // Selecting a claim highlights its subjects: a tested claim with none cannot be found from the scene (this was
      // the integrity rule tested-claims-name-subjects while test evidence was declared).
      unnamed.add(c.id);
      out.push({ code: 'evidence.claim-without-subjects', severity: 'error', entityId: c.id, path: ['subjects'],
        message: `Claim "${c.id}" is evidenced by tests (${e.data.ref}) but names no subjects, so selecting it highlights nothing in the scene.` });
    }
  }
  for (const p of x.facts.evidenceProblems ?? []) {
    out.push({ code: 'evidence.marker-invalid', severity: 'error', message: `${p.file}:${p.line}: ${p.message}` });
  }
  for (const e of model.byKind.evidence ?? []) {
    if (isDerivedEvidence(e) || e.data.kind !== 'test' || e.data.supports === false) continue;
    if (derivedKeys.has(`${e.data.claim}${SEP}${e.data.ref}`)) {
      out.push({ code: 'evidence.duplicates-derived', severity: 'error', entityId: e.id, path: ['ref'],
        message: `Evidence "${e.id}" declares that ${e.data.ref} evidences "${e.data.claim}", which the test's own marker already says: remove the declaration (declared evidence is for measurements, reviews, documents and contradicting evidence).` });
    }
  }
  return out;
}

/**
 * The model with the extracted facts as relationships, after the declared ones. The declared relationships are not
 * touched; `model.extraction` records what was read. Facts whose shape is unreadable leave the model unchanged.
 * The evidence the facts' test markers derive (derivedEvidence) is added after the declared evidence.
 * @param {Model} model @param {ExtractedFacts|null|undefined} facts
 * @returns {Model}
 */
export function attachExtracted(model, facts) {
  if (!facts || checkFacts(facts).length) return model;
  const stripped = stripExtracted(model);
  const extraction = liftExtracted(stripped, facts);
  const entities = extraction.edges.map((e) => edgeEntity(e, facts));
  const evidence = derivedEvidence(facts).filter((e) => !stripped.entities.has(e.id));
  extraction.evidenceIds = evidence.map((e) => e.id);
  const map = new Map(stripped.entities);
  for (const e of [...entities, ...evidence]) map.set(e.id, e);
  return /** @type {Model} */ ({ ...stripped, entities: map, byKind: { ...stripped.byKind, relationship: [...(stripped.byKind.relationship ?? []), ...entities], evidence: [...(stripped.byKind.evidence ?? []), ...evidence] }, extraction });
}

/** The model without any attached extracted or observed relationships. @param {Model} model @returns {Model} */
export function stripExtracted(model) {
  const m = /** @type {any} */ (model);
  if (!m.extraction && !m.observation) return model;
  const dropped = new Set([...(m.extraction?.relationshipIds ?? []), ...(m.extraction?.evidenceIds ?? []), ...(m.observation?.relationshipIds ?? [])]);
  const entities = new Map([...model.entities].filter(([id]) => !dropped.has(id)));
  const { extraction, observation, ...rest } = m;
  /** @type {Record<string, Entity[]>} */
  const byKind = { ...model.byKind, relationship: (model.byKind.relationship ?? []).filter((r) => !dropped.has(r.id)) };
  if (m.extraction?.evidenceIds?.length) byKind.evidence = (model.byKind.evidence ?? []).filter((e) => !dropped.has(e.id));
  return /** @type {Model} */ ({ ...rest, entities, byKind });
}

/** The extraction attached to a model, or null. @param {Model} model @returns {Extraction|null} */
export const extractionOf = (model) => /** @type {any} */ (model).extraction ?? null;

/**
 * The ids an extracted-facts change touches: the relationships the facts stand for in one model and not in the
 * other, and those whose file edges differ. Feed them to rederive and claimsToRecompute as an edit's `affected`.
 * @param {Model} before @param {Model} after @returns {string[]}
 */
export function extractedChange(before, after) {
  /** @param {Model} m @returns {Map<string, string>} */
  const sig = (m) => new Map(/** @type {[string, string][]} */ ([
    ...(extractionOf(m)?.edges ?? []).map((/** @type {ExtractedEdge} */ e) => [e.id, JSON.stringify([e.dynamic, e.sources])]),
    ...(extractionOf(m)?.evidenceIds ?? []).map((/** @type {string} */ id) => [id, JSON.stringify(m.entities.get(id)?.data ?? null)]),
  ]));
  const a = sig(before), b = sig(after);
  const out = new Set();
  for (const [id, s] of a) if (b.get(id) !== s) out.add(id);
  for (const [id, s] of b) if (a.get(id) !== s) out.add(id);
  return [...out].sort(byText);
}

/** Whether a relationship is an extracted fact. @param {Entity|{data: any}} r */
export const isExtracted = (r) => provenanceOf(r) === 'extracted';

// ---------------------------------------------------------------------------------------------
// Observed facts

/**
 * Observed interactions: for each event the recording shows at least once, every ordered pair of distinct components
 * where one's behaviors emit the event and the other's consume it. Each carries the recording and the count.
 * @param {Model} model @param {ObservedFacts} observed
 * @returns {{id: string, from: string, to: string, event: string, count: number, recording: string}[]}
 */
export function observedInteractions(model, observed) {
  const { emits, consumes } = eventExchange(model);
  /** @type {ReturnType<typeof observedInteractions>} */
  const out = [];
  for (const [event, count] of Object.entries(observed.events ?? {})) {
    if (!(count > 0)) continue;
    for (const [a, es] of emits) {
      if (!es.has(event)) continue;
      for (const [b, cs] of consumes) if (a !== b && cs.has(event)) out.push({ id: `${OBSERVED_PREFIX}${observed.recording.id}:${a}=>${b}:${event}`, from: a, to: b, event, count, recording: observed.recording.id });
    }
  }
  return out.sort((x, y) => byText(x.id, y.id));
}

/**
 * The model with the observed interactions of a recording as `notifies` relationships (provenance `observed`, the
 * recording named), one per ordered pair of components. Kept apart from the declared and the extracted ones.
 * @param {Model} model @param {ObservedFacts|null|undefined} observed @returns {Model}
 */
export function attachObserved(model, observed) {
  if (!observed || observed.format !== OBSERVED_FORMAT) return model;
  /** @type {Map<string, {from: string, to: string, events: Record<string, number>}>} */
  const pairs = new Map();
  for (const o of observedInteractions(model, observed)) {
    const k = `${o.from}\0${o.to}`;
    const p = pairs.get(k) ?? { from: o.from, to: o.to, events: {} };
    p.events[o.event] = o.count;
    pairs.set(k, p);
  }
  const entities = [...pairs.values()].map((p) => {
    const id = `${OBSERVED_PREFIX}${observed.recording.id}:${p.from}=>${p.to}`;
    return /** @type {Entity} */ (/** @type {unknown} */ ({ id, kind: 'relationship', owner: null, path: [id], loc: NO_LOC, data: { id, kind: 'notifies', from: p.from, to: p.to, provenance: 'observed', carries: Object.keys(p.events).sort(byText), recording: observed.recording, counts: p.events, description: `Observed in recording ${observed.recording.id}: ${Object.keys(p.events).length} event(s) passed from ${p.from} to ${p.to}.` } }));
  });
  const map = new Map(model.entities);
  for (const e of entities) map.set(e.id, e);
  return /** @type {Model} */ ({ ...model, entities: map, byKind: { ...model.byKind, relationship: [...(model.byKind.relationship ?? []), ...entities] }, observation: { observed, relationshipIds: entities.map((e) => e.id) } });
}

// ---------------------------------------------------------------------------------------------
// Reconciliation

/** The component lineage of an element: itself and its ancestors in the logical hierarchy. @param {Model} model @param {string} id */
function lineage(model, id) {
  const out = [];
  const seen = new Set();
  /** @type {string|undefined} */
  let cur = id;
  while (cur && !seen.has(cur)) {
    seen.add(cur);
    out.push(cur);
    const e = model.entities.get(cur);
    cur = typeof e?.data?.parent === 'string' ? e.data.parent : undefined;
  }
  return out;
}

/** The component that owns an endpoint (a module element's owner, a port's owner). @param {Model} model @param {string} id */
const componentId = (model, id) => componentOf(model, id)?.id ?? null;

/**
 * @typedef {{code: string, severity: 'warning'|'info', message: string, relationship?: string, from?: string, to?: string}} ReconcileDiagnostic
 * @typedef {{diagnostics: ReconcileDiagnostic[], summary: Record<string, number>, retiredCoverage?: any}} Reconciliation
 */

/**
 * Reconcile the declared relationships with the extracted facts attached to the model (and with an observation, when
 * one is attached). Nothing here is an error: an extracted dependency with no declared counterpart is not reported,
 * since the extracted fact is the dependency. Reported:
 *   reconcile.static-declared-redundant   a declared static dependency inside the extraction surface that extraction
 *                                         also finds: remove it, the extracted fact carries the edge;
 *   reconcile.static-declared-unwitnessed one that extraction does not find (remove it, or the code does not do it);
 *   reconcile.static-direction            declared one way, extracted only the other way;
 *   reconcile.static-kind                 declared a static import, extracted only dynamic imports;
 *   reconcile.observed-undeclared         an interaction the recording shows between components with no declared
 *                                         relationship of any kind between them (or their ancestors);
 *   reconcile.not-observed                a declared runtime interaction whose events the recording never shows
 *                                         (not observed, which is not false).
 * `info` diagnostics are facts to read; `warning` ones ask for a change of the specification.
 * @param {Model} model @returns {Reconciliation}
 */
export function reconcile(model) {
  const x = extractionOf(model);
  /** @type {ReconcileDiagnostic[]} */
  const diagnostics = [];
  const rels = (model.byKind.relationship ?? []).filter((r) => provenanceOf(r) === 'declared');
  /** @type {Record<string, number>} */
  const summary = { declaredRelationships: rels.length, extractedRelationships: x?.edges.length ?? 0, declaredStaticInSurface: 0, redundant: 0, unwitnessed: 0, reversed: 0, kindMismatch: 0, observedUndeclared: 0, notObserved: 0, unobservable: 0, externalImports: x?.external.length ?? 0 };
  if (x) {
    // Components inside the surface: those with a module element the facts cover.
    const inSurface = new Set(moduleDeclarations(model).filter((d) => !x.notExtracted.some((n) => n.component === d.component && n.path === d.path)).map((d) => d.component));
    const within = (/** @type {string} */ id) => [...inSurface].some((c) => lineage(model, c).includes(id));
    // Extracted component pairs: every extracted edge lifted to the lineage of its two components.
    /** @type {Map<string, ExtractedEdge>} */
    const pair = new Map();
    for (const e of x.edges) {
      const a = componentId(model, e.from), b = componentId(model, e.to);
      if (!a || !b || a === b) continue;
      for (const p of lineage(model, a)) for (const q of lineage(model, b)) if (p !== q) { const k = `${p}\0${q}`; if (!pair.has(k)) pair.set(k, e); }
    }
    const covers = (/** @type {string} */ a, /** @type {string} */ b) => pair.has(`${a}\0${b}`);
    const dynamicOnly = (/** @type {string} */ a, /** @type {string} */ b) => pair.get(`${a}\0${b}`)?.dynamic === true;
    for (const r of rels) {
      const info = kindInfo(model.meta, r.data.kind);
      if (info.class !== 'static') continue;
      const a = componentId(model, r.data.from), b = componentId(model, r.data.to);
      if (!a || !b || !within(a) || !within(b)) continue;
      summary.declaredStaticInSurface++;
      if (covers(a, b)) {
        if (r.data.kind === 'imports' && dynamicOnly(a, b)) { summary.kindMismatch++; diagnostics.push({ code: 'reconcile.static-kind', severity: 'warning', relationship: r.id, from: a, to: b, message: `Relationship "${r.id}" declares a static import from "${a}" to "${b}", but extraction finds only dynamic imports there.` }); }
        summary.redundant++;
        diagnostics.push({ code: 'reconcile.static-declared-redundant', severity: 'warning', relationship: r.id, from: a, to: b, message: `Relationship "${r.id}" declares a static dependency from "${a}" to "${b}" inside the extraction surface; the extracted facts carry this edge, so remove the declaration.` });
      } else if (covers(b, a)) {
        summary.reversed++;
        diagnostics.push({ code: 'reconcile.static-direction', severity: 'warning', relationship: r.id, from: a, to: b, message: `Relationship "${r.id}" declares a static dependency from "${a}" to "${b}", but extraction finds the imports the other way, from "${b}" to "${a}".` });
      } else {
        summary.unwitnessed++;
        diagnostics.push({ code: 'reconcile.static-declared-unwitnessed', severity: 'warning', relationship: r.id, from: a, to: b, message: `Relationship "${r.id}" declares a static dependency from "${a}" to "${b}" inside the extraction surface, and extraction finds no import there; remove it or correct the code.` });
      }
    }
    if (x.external.length) {
      const specs = [...new Set(x.external.map((e) => e.spec))].sort(byText);
      diagnostics.push({ code: 'reconcile.extracted-external', severity: 'info', message: `Extraction found ${x.external.length} imports of ${specs.length} specifiers outside the surface (packages, builtins, the standard library); no element stands for them here.` });
    }
    if (x.unowned.length) diagnostics.push({ code: 'reconcile.file-unowned', severity: 'warning', message: `${x.unowned.length} extracted files belong to no module element: ${x.unowned.slice(0, 5).join(', ')}${x.unowned.length > 5 ? ', ...' : ''}.` });
  }

  const obs = /** @type {any} */ (model).observation?.observed;
  if (obs) {
    const { emits, consumes } = eventExchange(model);
    const seenEvents = new Set(Object.entries(obs.events).filter(([, n]) => /** @type {number} */ (n) > 0).map(([e]) => e));
    // Any declared relationship of any provenance except observed ones, between lineages, counts as a counterpart.
    const base = (model.byKind.relationship ?? []).filter((r) => provenanceOf(r) !== 'observed');
    const edge = new Set(base.map((r) => `${componentId(model, r.data.from)}\0${componentId(model, r.data.to)}`));
    const declaredBetween = (/** @type {string} */ a, /** @type {string} */ b) => lineage(model, a).some((p) => lineage(model, b).some((q) => edge.has(`${p}\0${q}`)));
    for (const o of observedInteractions(model, obs)) {
      if (!declaredBetween(o.from, o.to)) { summary.observedUndeclared++; diagnostics.push({ code: 'reconcile.observed-undeclared', severity: 'warning', from: o.from, to: o.to, message: `Recording ${o.recording} shows event "${o.event}" passing from "${o.from}" to "${o.to}" ${o.count} time(s), and no relationship is declared between them.` }); }
    }
    void consumes; void emits;
    for (const r of rels) {
      if (kindInfo(model.meta, r.data.kind).class === 'static') continue;
      // The events a relationship stands for: those it carries, and those one end's behaviors emit and the other's consume.
      const a = componentId(model, r.data.from), b = componentId(model, r.data.to);
      const carried = [...new Set([
        ...(Array.isArray(r.data.carries) ? r.data.carries.filter((/** @type {any} */ c) => typeof c === 'string' && model.entities.get(c)?.kind === 'event') : []),
        ...(a && b && a !== b ? eventsBetween(model, a, b).forward : []),
      ])];
      if (!carried.length) { summary.unobservable++; continue; }
      if (carried.some((/** @type {string} */ c) => seenEvents.has(c))) continue;
      summary.notObserved++;
      diagnostics.push({ code: 'reconcile.not-observed', severity: 'info', relationship: r.id, message: `Relationship "${r.id}" carries ${carried.map((/** @type {string} */ c) => `"${c}"`).join(', ')}; recording ${obs.recording.id} shows none of them. That is not observed in this recording, which does not make the relationship false.` });
    }
  }
  return { diagnostics, summary };
}

/**
 * For each declared relationship, the extracted relationships that cover it at component granularity: an extracted
 * edge from a module of the source (or a descendant of it) to a module of the target (or a descendant). Used to show
 * that retiring a declared static dependency loses nothing.
 * @param {Model} model relationships still declared in it are looked up by id; pass the model from before the retirement
 * @param {string[]} ids @param {Extraction} x
 * @returns {{id: string, from: string, to: string, covered: boolean, by: string[]}[]}
 */
export function coverageOf(model, ids, x) {
  /** @type {Map<string, string[]>} */
  const pair = new Map();
  for (const e of x.edges) {
    const a = componentId(model, e.from), b = componentId(model, e.to);
    if (!a || !b) continue;
    for (const p of lineage(model, a)) for (const q of lineage(model, b)) { const k = `${p}\0${q}`; (pair.get(k) ?? pair.set(k, []).get(k))?.push(e.id); }
  }
  return ids.map((id) => {
    const r = model.entities.get(id);
    const from = String(r?.data.from), to = String(r?.data.to);
    const by = pair.get(`${from}\0${to}`) ?? [];
    return { id, from, to, covered: by.length > 0, by: by.slice(0, 3) };
  });
}

/**
 * What the relationships a check reads rest on: counts by provenance, and a plain label.
 * @param {Iterable<Entity|{data: any}>} relationships
 * @returns {{counts: Record<string, number>, basis: 'declared-only'|'extracted'|'observed'|'extracted+observed'|'none', text: string}}
 */
export function witnessBasis(relationships) {
  /** @type {Record<string, number>} */
  const counts = {};
  for (const r of relationships) { const p = provenanceOf(r); counts[p] = (counts[p] ?? 0) + 1; }
  const ex = (counts.extracted ?? 0) > 0, ob = (counts.observed ?? 0) > 0;
  const basis = ex && ob ? 'extracted+observed' : ex ? 'extracted' : ob ? 'observed' : Object.keys(counts).length ? 'declared-only' : 'none';
  const mix = Object.keys(counts).sort(byText).map((k) => `${counts[k]} ${k}`).join(', ');
  const text = basis === 'declared-only' ? `The relationships it reads are declared by authors (${mix}); nothing checked them against the code.`
    : basis === 'none' ? 'It reads no relationships.'
    : `The relationships it reads are ${mix}.${ex ? ` ${STATIC_ONLY}` : ''}${ob ? ' Observed relationships come from a recording and say only that the events occurred there.' : ''}`;
  return { counts, basis, text };
}

const GRAPH_METHODS = ['no-relationship', 'reachable', 'only-via', 'acyclic'];

/**
 * What the relationships a graph claim reads rest on: the relationships of the kinds and classes the claim follows,
 * by provenance. Null for a claim that reads no relationship graph.
 * @param {Model} model @param {any} ev the claim's `evaluate`
 */
export function claimBasis(model, ev) {
  if (!ev || !GRAPH_METHODS.includes(ev.method)) return null;
  const kinds = Array.isArray(ev.kinds) ? ev.kinds : null;
  const classes = Array.isArray(ev.classes) ? ev.classes : null;
  return witnessBasis((model.byKind.relationship ?? []).filter((r) => (!kinds || kinds.includes(r.data.kind)) && (!classes || classes.includes(kindInfo(model.meta, r.data.kind).class))));
}

export { elementsOf };
