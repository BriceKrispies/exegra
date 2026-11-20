// Claim strength: how strong the check behind a claim's status is, and what it reads. A status says
// that an evaluator checked a claim within its scope; it does not say how much that check could have
// found. This module adds two attributes per claim and per integrity rule, and never changes a status:
//
//   check      holds-by-construction | restated-scenario | single-trace | explored | refined |
//              structural | data-model | lean-theorem | sampled | test | evidence | integrity | none
//   grounding  bound | partly-bound | self-contained | not-applicable
//
// The definitions, the alternatives considered and why are the decision dec-claim-check-and-grounding
// in specs/exegra/spec.jsonc; docs/claims-and-evidence.md, "Check strength and grounding", explains
// them for readers. The analysis is static and deterministic: it reads the model, and runs one
// scenario only to decide restated-scenario.

import { parseExpr, exprRefs, valueEquals } from './expr.js';
import { parseRule } from './integrity.js';
import { runScenario as engineRunScenario } from './engine.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

/**
 * @typedef {{
 *   check: string, grounding: string,
 *   variables?: {variable: string, nominal: string, faultTransitions: string[]}[],
 *   transitions?: string[], blocked?: string[],
 *   reads?: string[], free?: string[], scenarios?: string[]
 * }} StrengthDetails
 *   check and grounding: one sentence each saying why; variables: for holds-by-construction of a state
 *   invariant, each variable read with what nominal transitions can do to it and the fault transitions
 *   that assign it; transitions: the fault transitions that are the only producers of an occurrence;
 *   blocked: nominal producers whose guard is false for every value nominal runs give; reads: what the
 *   grounding rests on; free: payload fields of events that belong to no contract, read by a guard or
 *   an effect; scenarios: the hand-written scenarios a single-trace claim runs.
 * @typedef {{entity: 'claim'|'integrityRule', check: string, grounding: string, details: StrengthDetails}} Strength
 * @typedef {{
 *   existing?: Set<string>|null,
 *   explored?: Set<string>|null,
 *   runScenario?: ((model: Model, scenarioId: string) => any)|null
 * }} StrengthOptions
 *   existing: the ids of the entities the platform already has (admit passes the model before the change);
 *   an entity outside it anchors nothing. Absent: every entity of the model counts.
 *   explored: the claims an exhaustive exploration (exegra prove) found to hold (WG-5280 records them).
 *   runScenario: runs one scenario for restated-scenario; the engine by default.
 */

export const CHECKS = /** @type {const} */ (['holds-by-construction', 'restated-scenario', 'single-trace', 'explored', 'refined', 'structural', 'data-model', 'lean-theorem', 'sampled', 'test', 'evidence', 'integrity', 'none']);
export const GROUNDINGS = /** @type {const} */ (['bound', 'partly-bound', 'self-contained', 'not-applicable']);
/** The checks that cannot fail on a correct model: admit.claim-vacuous. */
export const VACUOUS_CHECKS = new Set(['holds-by-construction', 'restated-scenario']);

const TRACE_METHODS = new Set(['state-invariant', 'precedes', 'eventually', 'never']);
const STRUCTURAL_METHODS = new Set(['no-relationship', 'reachable', 'only-via', 'has-port', 'property-defined', 'acyclic', 'implementation-language']);
/** Most combinations of values the value analysis enumerates before it gives up. */
const MAX_COMBINATIONS = 4096;

/**
 * The strength of every claim and integrity rule of a model, by id.
 * @param {Model} model @param {StrengthOptions} [opts]
 * @returns {Map<string, Strength>}
 */
export function claimStrength(model, opts = {}) {
  const ctx = context(model, opts);
  /** @type {Map<string, Strength>} */
  const out = new Map();
  for (const claim of model.byKind.claim ?? []) out.set(claim.id, claimEntry(ctx, claim));
  for (const rule of model.byKind.integrityRule ?? []) out.set(rule.id, ruleEntry(ctx, rule));
  return out;
}

/**
 * Counts by check and by grounding, for claims and for integrity rules.
 * @param {Map<string, Strength>} strength
 */
export function strengthCounts(strength) {
  /** @type {{claims: {check: Record<string, number>, grounding: Record<string, number>}, integrityRules: {grounding: Record<string, number>}}} */
  const out = { claims: { check: {}, grounding: {} }, integrityRules: { grounding: {} } };
  for (const s of strength.values()) {
    if (s.entity === 'claim') {
      out.claims.check[s.check] = (out.claims.check[s.check] ?? 0) + 1;
      out.claims.grounding[s.grounding] = (out.claims.grounding[s.grounding] ?? 0) + 1;
    } else out.integrityRules.grounding[s.grounding] = (out.integrityRules.grounding[s.grounding] ?? 0) + 1;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

/** @param {Model} model @param {StrengthOptions} opts */
function context(model, opts) {
  /** @type {Map<string, Entity[]>} */
  const transitions = new Map();
  for (const t of model.byKind.transition ?? []) {
    const list = transitions.get(/** @type {string} */ (t.owner)) ?? [];
    list.push(t);
    transitions.set(/** @type {string} */ (t.owner), list);
  }
  const existing = opts.existing ?? null;
  const ctx = {
    model,
    transitions,
    existing,
    explored: opts.explored ?? null,
    runScenario: opts.runScenario ?? ((/** @type {Model} */ m, /** @type {string} */ id) => engineRunScenario(m, id)),
    /** @param {string} id */
    platform: (id) => !existing || existing.has(id),
    /** @type {Map<string, BehaviorGrounding>} */
    behaviors: new Map(),
  };
  ctx.behaviors = behaviorGroundings(ctx);
  return ctx;
}

/** @typedef {ReturnType<typeof context>} Ctx */

/** @param {Ctx} ctx @param {string} id @param {string} kind */
function entityOf(ctx, id, kind) {
  const e = typeof id === 'string' ? ctx.model.entities.get(id) : undefined;
  return e && e.kind === kind ? e : undefined;
}

/** @param {any} v @returns {any[]} */
const arr = (v) => (Array.isArray(v) ? v : v === undefined || v === null ? [] : [v]);
/** @param {string[]} xs */
const uniq = (xs) => [...new Set(xs)];
/** @param {string[]} xs */
const quoted = (xs) => xs.map((x) => `"${x}"`).join(', ');

// ---------------------------------------------------------------------------
// Claims
// ---------------------------------------------------------------------------

/** @param {Ctx} ctx @param {Entity} claim @returns {Strength} */
function claimEntry(ctx, claim) {
  const ev = claim.data.evaluate && typeof claim.data.evaluate === 'object' ? claim.data.evaluate : null;
  const method = ev && typeof ev.method === 'string' ? ev.method : null;
  /** @param {string} check @param {string} why @param {{grounding: string, why: string, reads?: string[], free?: string[]}} g @param {Partial<StrengthDetails>} [more] @returns {Strength} */
  const entry = (check, why, g, more = {}) => ({
    entity: 'claim', check, grounding: g.grounding,
    details: { check: why, grounding: g.why, ...(g.reads?.length ? { reads: g.reads } : {}), ...(g.free?.length ? { free: g.free } : {}), ...more },
  });
  const notApplicable = (/** @type {string} */ why) => ({ grounding: 'not-applicable', why });

  if (!method) return entry('none', 'The claim declares no evaluation method.', notApplicable('Nothing is evaluated.'));
  if (ctx.model.meta?.verificationMethods && Object.hasOwn(ctx.model.meta.verificationMethods, method)) {
    return entry(evidenceCheck(ctx, claim), `Verified outside Exegra by the method "${method}"; the status comes from evidence.`, notApplicable('The status rests on evidence outside the model.'));
  }
  if (method === 'external-evidence') {
    const check = evidenceCheck(ctx, claim);
    return entry(check, check === 'test' ? 'The status comes from attached test evidence.' : 'The status comes from attached evidence that is not a test.', notApplicable('The status rests on evidence outside the model.'));
  }
  if (STRUCTURAL_METHODS.has(method)) {
    return entry('structural', `Decided over the whole declared component graph by "${method}".`, { grounding: 'bound', why: 'Reads the declared components and relationships of the model.', reads: ['components and relationships'] });
  }
  if (method === 'data-model') return entry('data-model', 'Decided over the records and copies of the model by the data rules.', dataModelGrounding(ctx, ev));
  if (method === 'lean-theorem') {
    const about = arr(ev.about).filter((a) => typeof a === 'string');
    return entry('lean-theorem', `A theorem of the Lean core, "${ev.theorem}", checked by the Lean kernel; it covers every input.`, { grounding: 'bound', why: `States a property of the Lean definitions${about.length ? ` ${quoted(about)}` : ''}.`, reads: [`theorem "${ev.theorem}"`, ...about.map((a) => `definition "${a}"`)] });
  }
  if (method === 'refines') return refinesEntry(ctx, ev, entry);
  if (method === 'metric-bound') {
    const scenarios = arr(ev.scenarios).filter((s) => typeof s === 'string');
    return entry('sampled', 'A statistical bound over seeded runs of the listed scenarios: model-holds at best, never verified.', combine(ctx, scenarioBehaviors(ctx, scenarios)), { scenarios });
  }
  if (TRACE_METHODS.has(method)) return traceEntry(ctx, claim, ev, entry);
  return entry('none', `This build does not evaluate the method "${method}".`, notApplicable('Nothing is evaluated.'));
}

/** @param {Ctx} ctx @param {Entity} claim */
function evidenceCheck(ctx, claim) {
  return (ctx.model.byKind.evidence ?? []).some((e) => e.data.claim === claim.id && e.data.kind === 'test') ? 'test' : 'evidence';
}

/** @param {Ctx} ctx @param {any} ev */
function dataModelGrounding(ctx, ev) {
  const records = arr(ev.records).filter((r) => typeof r === 'string');
  if (records.length && !records.some((r) => ctx.platform(r))) {
    return { grounding: 'partly-bound', why: `Reads only records the change adds (${quoted(records)}).`, reads: records.map((r) => `record "${r}"`) };
  }
  return { grounding: 'bound', why: records.length ? `Reads the records ${quoted(records)} and their copies.` : 'Reads every record and copy of the model.', reads: records.length ? records.map((r) => `record "${r}"`) : ['records and copies'] };
}

/** @param {Ctx} ctx @param {any} ev @param {Function} entry */
function refinesEntry(ctx, ev, entry) {
  const impl = entityOf(ctx, ev.behavior, 'behavior');
  const target = impl && typeof impl.data.refines === 'string' ? impl.data.refines : null;
  const why = `The behavior "${ev.behavior}" is checked step by step against the behavior it refines${target ? `, "${target}"` : ''}, on the traces of its scenarios.`;
  if (target && ctx.platform(target) && entityOf(ctx, target, 'behavior')) {
    return entry('refined', why, { grounding: 'bound', why: `Refines the existing behavior "${target}".`, reads: [`refines behavior "${target}"`] });
  }
  return entry('refined', why, combine(ctx, impl ? [impl.id] : []));
}

/**
 * @param {Ctx} ctx @param {Entity} claim @param {any} ev
 * @param {(check: string, why: string, g: any, more?: Partial<StrengthDetails>) => Strength} entry
 */
function traceEntry(ctx, claim, ev, entry) {
  const scenarioIds = arr(ev.scenarios).filter((s) => typeof s === 'string' && entityOf(ctx, s, 'scenario'));
  const enabled = enabledBy(ctx, scenarioIds);
  const read = readBehaviors(ctx, ev, scenarioIds);
  const grounding = combine(ctx, read);

  const hbc = holdsByConstruction(ctx, ev, scenarioIds, enabled);
  if (hbc) return entry('holds-by-construction', hbc.why, grounding, hbc.more);
  if (ev.method === 'state-invariant') {
    const restated = restatedScenario(ctx, ev, scenarioIds, enabled);
    if (restated) return entry('restated-scenario', restated, grounding);
  }
  if (ctx.explored?.has(claim.id)) return entry('explored', 'An exhaustive exploration of its scenario found that the claim holds in every configuration within the bound.', grounding);
  const refining = read.filter((b) => {
    const r = entityOf(ctx, b, 'behavior')?.data.refines;
    return typeof r === 'string' && ctx.platform(r) && entityOf(ctx, r, 'behavior');
  });
  if (read.length && refining.length === read.length) {
    return entry('refined', `Every behavior the claim reads refines an existing behavior (${quoted(refining)}); the claim itself is checked on the traces of its scenarios.`, grounding);
  }
  const n = scenarioIds.length;
  return entry('single-trace', `Decided by running ${n === 1 ? 'one hand-written scenario' : `${n} hand-written scenarios`} (${quoted(scenarioIds)}), with no exhaustive exploration and no refinement: a check of these traces, not of all executions.`, grounding, { scenarios: scenarioIds });
}

/** The faultOnly transitions that faults of the scenarios enable. @param {Ctx} ctx @param {string[]} scenarioIds */
function enabledBy(ctx, scenarioIds) {
  /** @type {Set<string>} */
  const out = new Set();
  for (const s of scenarioIds) {
    for (const f of arr(ctx.model.entities.get(s)?.data.faults)) {
      const fault = entityOf(ctx, f, 'fault');
      if (fault?.data.kind === 'enable-transition' && typeof fault.data.transition === 'string') out.add(fault.data.transition);
    }
  }
  return out;
}

/** @param {Entity} t @param {Set<string>} enabled */
const nominal = (t, enabled) => t.data.faultOnly !== true || enabled.has(t.id);

/** The behaviors of the scenarios. @param {Ctx} ctx @param {string[]} scenarioIds */
function scenarioBehaviors(ctx, scenarioIds) {
  return uniq(scenarioIds.flatMap((s) => arr(ctx.model.entities.get(s)?.data.behaviors).filter((b) => typeof b === 'string')));
}

/**
 * The behaviors a trace claim reads: those its expression names, the owner of a transition matcher, and
 * for an event matcher the behaviors of its scenarios that react to or emit the event.
 * @param {Ctx} ctx @param {any} ev @param {string[]} scenarioIds
 */
function readBehaviors(ctx, ev, scenarioIds) {
  const inScenarios = scenarioBehaviors(ctx, scenarioIds);
  /** @type {string[]} */
  const out = [];
  const fromExpr = (/** @type {any} */ src) => {
    if (typeof src !== 'string') return;
    const p = parseExpr(src);
    if (!p.ok) return;
    for (const path of exprRefs(p.ast)) if (path.length >= 2 && entityOf(ctx, path[0], 'behavior')) out.push(path[0]);
  };
  const fromMatcher = (/** @type {any} */ m) => {
    if (!m || typeof m !== 'object') return;
    if (typeof m.transition === 'string') {
      const t = entityOf(ctx, m.transition, 'transition');
      if (t?.owner) out.push(t.owner);
    } else if (typeof m.event === 'string') {
      for (const b of inScenarios) {
        if ((ctx.transitions.get(b) ?? []).some((t) => t.data.on === m.event || effectsOf(t).some((fx) => emitsEvent(fx) === m.event))) out.push(b);
      }
    }
  };
  fromExpr(ev.expr);
  fromMatcher(ev.occurs);
  fromMatcher(ev.first);
  fromMatcher(ev.then);
  return out.length ? uniq(out) : inScenarios;
}

/** @param {Entity} t @returns {any[]} */
const effectsOf = (t) => arr(t.data.effects).filter((fx) => fx && typeof fx === 'object');
/** The event an effect emits (an emit, a timer, or a resource outcome), or undefined. @param {any} fx */
const emitsEvent = (fx) => (typeof fx.emit === 'string' ? fx.emit : typeof fx.then === 'string' ? fx.then : typeof fx.refused === 'string' ? fx.refused : undefined);

// ---------------------------------------------------------------------------
// holds-by-construction
// ---------------------------------------------------------------------------

/**
 * Why no nominal run can violate the claim, or null.
 * @param {Ctx} ctx @param {any} ev @param {string[]} scenarioIds @param {Set<string>} enabled
 * @returns {{why: string, more: Partial<StrengthDetails>}|null}
 */
function holdsByConstruction(ctx, ev, scenarioIds, enabled) {
  if (ev.method === 'state-invariant') return invariantByConstruction(ctx, ev.expr, enabled);
  if (ev.method === 'never') {
    const p = onlyFaultProduces(ctx, ev.occurs, scenarioIds, enabled);
    const what = typeof ev.occurs?.transition === 'string' && p?.faults.length === 1 && !p.blocked.length
      ? `The transition "${ev.occurs.transition}" is faultOnly and no fault of the claim's scenarios enables it`
      : p && `The ${matcherText(ev.occurs)} can be produced only by ${producersText(p)}`;
    return p && { why: `${what}, so no run without the defect can violate the claim.`, more: { transitions: p.faults, ...(p.blocked.length ? { blocked: p.blocked } : {}) } };
  }
  if (ev.method === 'precedes') {
    const p = onlyFaultProduces(ctx, ev.then, scenarioIds, enabled);
    return p && { why: `The ${matcherText(ev.then)} can be produced only by ${producersText(p)}, so in a run without the defect there is nothing to order.`, more: { transitions: p.faults, ...(p.blocked.length ? { blocked: p.blocked } : {}) } };
  }
  return null;
}

/** @param {any} m */
const matcherText = (m) => (m && typeof m.event === 'string' ? `event "${m.event}"` : `transition "${m?.transition}"`);
/** @param {{faults: string[], blocked: string[]}} p */
function producersText(p) {
  const parts = [];
  if (p.faults.length) parts.push(`the fault transition${p.faults.length === 1 ? '' : 's'} ${quoted(p.faults)}`);
  if (p.blocked.length) parts.push(`the transition${p.blocked.length === 1 ? '' : 's'} ${quoted(p.blocked)}, whose guard is false for every value nominal runs give its variables`);
  return parts.join(' and ');
}

/**
 * When an occurrence can be produced only by faultOnly transitions (that the claim's scenarios do not
 * enable) or by nominal transitions whose guard can never hold: those transitions; otherwise null. An
 * occurrence that the scenario script delivers or a fault injects is produced by the scenario: null.
 * @param {Ctx} ctx @param {any} m @param {string[]} scenarioIds @param {Set<string>} enabled
 * @returns {{faults: string[], blocked: string[]}|null}
 */
function onlyFaultProduces(ctx, m, scenarioIds, enabled) {
  if (!m || typeof m !== 'object') return null;
  /** @type {Entity[]} */
  let producers;
  if (typeof m.transition === 'string') {
    const t = entityOf(ctx, m.transition, 'transition');
    if (!t) return null;
    producers = [t];
  } else if (typeof m.event === 'string') {
    for (const s of scenarioIds) {
      const sc = ctx.model.entities.get(s);
      if (arr(sc?.data.steps).some((st) => st?.event === m.event)) return null;
      if (arr(sc?.data.faults).some((f) => { const d = entityOf(ctx, f, 'fault')?.data; return d?.kind === 'inject-event' && d.event === m.event; })) return null;
    }
    producers = scenarioBehaviors(ctx, scenarioIds).flatMap((b) => (ctx.transitions.get(b) ?? []).filter((t) => effectsOf(t).some((fx) => emitsEvent(fx) === m.event)));
    if (!producers.length) return null;
  } else return null;
  /** @type {string[]} */ const faults = [];
  /** @type {string[]} */ const blocked = [];
  for (const t of producers) {
    if (!nominal(t, enabled)) { faults.push(t.id); continue; }
    if (typeof t.data.guard === 'string' && t.data.guard.trim() && guardNeverHolds(ctx, t, enabled)) { blocked.push(t.id); continue; }
    return null;
  }
  return { faults, blocked };
}

/** @param {Ctx} ctx @param {Entity} t @param {Set<string>} enabled */
function guardNeverHolds(ctx, t, enabled) {
  const p = parseExpr(t.data.guard);
  if (!p.ok) return false;
  const verdict = everyCombination(ctx, p.ast, enabled, /** @type {string} */ (t.owner));
  return verdict === 'false';
}

/**
 * A state invariant that every value nominal runs can give its references satisfies.
 * @param {Ctx} ctx @param {any} src @param {Set<string>} enabled
 * @returns {{why: string, more: Partial<StrengthDetails>}|null}
 */
function invariantByConstruction(ctx, src, enabled) {
  if (typeof src !== 'string') return null;
  const p = parseExpr(src);
  if (!p.ok) return null;
  if (everyCombination(ctx, p.ast, enabled, null) !== 'true') return null;
  /** @type {{variable: string, nominal: string, faultTransitions: string[]}[]} */
  const variables = [];
  for (const path of uniqPaths(exprRefs(p.ast))) {
    if (path.length !== 2 || path[1] === 'state') continue;
    const b = entityOf(ctx, path[0], 'behavior');
    if (!b) continue;
    const assigns = (ctx.transitions.get(b.id) ?? []).filter((t) => effectsOf(t).some((fx) => fx.set === path[1]));
    const nom = assigns.filter((t) => nominal(t, enabled));
    const d = domainOf(ctx, b.id, path[1], enabled);
    const text = !nom.length ? 'assigned by no nominal transition'
      : d && d.t === 'finite' ? `set by nominal transitions only to ${d.values.map((v) => JSON.stringify(v)).join(' or ')}`
        : `set by nominal transitions only together with ${quoted(d && d.t === 'opaque' ? d.peers.filter((x) => x !== `${b.id}.${path[1]}`) : [])}, to the same expression`;
    variables.push({ variable: `${b.id}.${path[1]}`, nominal: text, faultTransitions: assigns.filter((t) => !nominal(t, enabled)).map((t) => t.id) });
  }
  const faults = uniq(variables.flatMap((v) => v.faultTransitions));
  const what = variables.length ? variables.map((v) => `"${v.variable}" is ${v.nominal}`).join('; ') : 'the expression reads no variable';
  return {
    why: `\`${src}\` is true for every value nominal runs can give what it reads: ${what}${faults.length ? `. Only the fault transition${faults.length === 1 ? '' : 's'} ${quoted(faults)} can make it false` : ''}.`,
    more: { variables, ...(faults.length ? { transitions: faults } : {}) },
  };
}

/** @param {string[][]} paths */
function uniqPaths(paths) {
  const seen = new Set();
  return paths.filter((p) => { const k = p.join('.'); if (seen.has(k)) return false; seen.add(k); return true; });
}

// The value analysis. A reference takes a finite list of concrete values, or an opaque value: a value
// the analysis does not know, equal only to itself (variables always set together to the same
// expression share one). Evaluation is three-valued; UNKNOWN absorbs everything it cannot decide.

const UNKNOWN = Symbol('unknown');

/**
 * @typedef {{t: 'finite', values: any[]} | {t: 'opaque', cls: string, peers: string[]}} Domain
 */

/**
 * Whether an expression is true ('true'), false ('false') for every combination of the values nominal
 * runs can give its references, or neither ('unknown').
 * @param {Ctx} ctx @param {any} ast @param {Set<string>} enabled @param {string|null} self the behavior whose bare names the expression reads (a guard), or null (a claim)
 */
function everyCombination(ctx, ast, enabled, self) {
  const paths = uniqPaths(exprRefs(ast));
  /** @type {{key: string, values: any[]}[]} */
  const axes = [];
  let size = 1;
  for (const path of paths) {
    const values = valuesOf(ctx, path, enabled, self);
    if (values === null) return 'unknown';
    axes.push({ key: path.join('.'), values });
    size *= values.length;
    if (size > MAX_COMBINATIONS) return 'unknown';
  }
  let sawTrue = false;
  let sawFalse = false;
  /** @type {Map<string, any>} */
  const env = new Map();
  /** @param {number} i @returns {boolean} false to stop */
  const walk = (i) => {
    if (i === axes.length) {
      const v = evalTri(ast, env);
      if (v === true) sawTrue = true;
      else if (v === false) sawFalse = true;
      else { sawTrue = sawFalse = true; return false; }
      return !(sawTrue && sawFalse);
    }
    for (const v of axes[i].values) {
      env.set(axes[i].key, v);
      if (!walk(i + 1)) return false;
    }
    return true;
  };
  walk(0);
  if (sawTrue && !sawFalse) return 'true';
  if (sawFalse && !sawTrue) return 'false';
  return 'unknown';
}

/**
 * The values a reference can take in nominal runs, or null when the analysis does not cover it.
 * @param {Ctx} ctx @param {string[]} path @param {Set<string>} enabled @param {string|null} self
 * @returns {any[]|null}
 */
function valuesOf(ctx, path, enabled, self) {
  if (path.length === 1 && path[0] === 'time') return [UNKNOWN];
  if (path[0] === 'event') return [UNKNOWN];
  let behavior;
  let name;
  if (path.length === 1 && self) { behavior = self; name = path[0]; } else if (path.length === 2) { behavior = path[0]; name = path[1]; } else return null;
  const b = entityOf(ctx, behavior, 'behavior');
  if (!b || b.data.instances) return null;
  if (name === 'state' && !arr(b.data.variables).some((v) => v?.name === 'state')) return reachableStates(ctx, b, enabled);
  const d = domainOf(ctx, b.id, name, enabled);
  if (!d) return null;
  return d.t === 'finite' ? d.values : [{ opaque: d.cls }];
}

/** States reachable from the initial state over nominal transitions, guards ignored. @param {Ctx} ctx @param {Entity} b @param {Set<string>} enabled */
function reachableStates(ctx, b, enabled) {
  const seen = new Set([b.data.initial]);
  const queue = [b.data.initial];
  const ts = (ctx.transitions.get(b.id) ?? []).filter((t) => nominal(t, enabled));
  while (queue.length) {
    const s = queue.shift();
    for (const t of ts) if (t.data.from === s && !seen.has(t.data.to)) { seen.add(t.data.to); queue.push(t.data.to); }
  }
  return [...seen];
}

/**
 * The values a variable can take in nominal runs: finite when every nominal assignment is a literal,
 * opaque otherwise (shared with the variables that start equal and are always set with it to the same
 * expression, one that reads none of the behavior's own variables). null for an undeclared variable.
 * @param {Ctx} ctx @param {string} behaviorId @param {string} name @param {Set<string>} enabled
 * @returns {Domain|null}
 */
function domainOf(ctx, behaviorId, name, enabled) {
  const b = entityOf(ctx, behaviorId, 'behavior');
  const vars = arr(b?.data.variables).filter((v) => v && typeof v.name === 'string');
  const decl = vars.find((v) => v.name === name);
  if (!b || !decl) return null;
  const ts = (ctx.transitions.get(b.id) ?? []).filter((t) => nominal(t, enabled));
  /** @param {string} v */
  const assignsOf = (v) => ts.flatMap((t) => effectsOf(t).filter((fx) => fx.set === v).map((fx) => ({ t: t.id, to: fx.to })));
  const assigns = assignsOf(name);
  const literals = assigns.map((a) => literalOf(a.to));
  if (literals.every((l) => l.ok)) {
    /** @type {any[]} */
    const values = [decl.initial];
    for (const l of literals) if (!values.some((v) => valueEquals(v, l.value))) values.push(l.value);
    return { t: 'finite', values };
  }
  const own = new Set(vars.map((v) => v.name));
  const readsOwn = (/** @type {any} */ to) => {
    if (typeof to !== 'string') return false;
    const p = parseExpr(to);
    return !p.ok || exprRefs(p.ast).some((path) => path.length === 1 && own.has(path[0]));
  };
  const signature = (/** @type {{t: string, to: any}[]} */ as) => JSON.stringify(as.map((a) => [a.t, a.to]).sort());
  const key = `${behaviorId}.${name}`;
  if (assigns.some((a) => readsOwn(a.to))) return { t: 'opaque', cls: key, peers: [key] };
  const sig = signature(assigns);
  const peers = vars.filter((v) => valueEquals(v.initial, decl.initial) && signature(assignsOf(v.name)) === sig && !assignsOf(v.name).some((a) => readsOwn(a.to))).map((v) => `${behaviorId}.${v.name}`);
  return { t: 'opaque', cls: `${behaviorId}:${sig}`, peers };
}

/** @param {any} to @returns {{ok: true, value: any} | {ok: false}} */
function literalOf(to) {
  if (typeof to !== 'string') return { ok: true, value: to };
  const p = parseExpr(to);
  if (p.ok && p.ast.t === 'lit') return { ok: true, value: p.ast.v };
  if (p.ok && p.ast.t === 'un' && p.ast.op === '-' && p.ast.a.t === 'lit' && typeof p.ast.a.v === 'number') return { ok: true, value: -p.ast.a.v };
  return { ok: false };
}

/** @param {any} v */
const isOpaque = (v) => v !== null && typeof v === 'object' && typeof v.opaque === 'string';

/**
 * Three-valued evaluation: true, false, a value, or UNKNOWN.
 * @param {any} ast @param {Map<string, any>} env @returns {any}
 */
function evalTri(ast, env) {
  switch (ast.t) {
    case 'lit': return ast.v;
    case 'ref': {
      const k = ast.path.join('.');
      return env.has(k) ? env.get(k) : UNKNOWN;
    }
    case 'un': {
      const a = evalTri(ast.a, env);
      if (ast.op === '!') return typeof a === 'boolean' ? !a : UNKNOWN;
      return typeof a === 'number' ? -a : UNKNOWN;
    }
    case 'bin': {
      const op = ast.op;
      if (op === '&&' || op === '||' || op === '=>') {
        const a = evalTri(ast.a, env);
        if (op === '&&' && a === false) return false;
        if (op === '||' && a === true) return true;
        if (op === '=>' && a === false) return true;
        const b = evalTri(ast.b, env);
        if (op === '&&') return a === true ? (typeof b === 'boolean' ? b : UNKNOWN) : b === false ? false : UNKNOWN;
        if (op === '||') return a === false ? (typeof b === 'boolean' ? b : UNKNOWN) : b === true ? true : UNKNOWN;
        return a === true ? (typeof b === 'boolean' ? b : UNKNOWN) : b === true ? true : UNKNOWN;
      }
      const a = evalTri(ast.a, env);
      const b = evalTri(ast.b, env);
      if (a === UNKNOWN || b === UNKNOWN) return UNKNOWN;
      if (isOpaque(a) || isOpaque(b)) {
        const same = isOpaque(a) && isOpaque(b) && a.opaque === b.opaque;
        if (!same) return UNKNOWN;
        if (op === '==' || op === '<=' || op === '>=') return true;
        if (op === '!=' || op === '<' || op === '>') return false;
        return UNKNOWN;
      }
      if (op === '==') return valueEquals(a, b);
      if (op === '!=') return !valueEquals(a, b);
      if (op === '+' && typeof a === 'string' && typeof b === 'string') return a + b;
      if (typeof a !== 'number' || typeof b !== 'number') return UNKNOWN;
      switch (op) {
        case '<': return a < b;
        case '<=': return a <= b;
        case '>': return a > b;
        case '>=': return a >= b;
        case '+': return a + b;
        case '-': return a - b;
        case '*': return a * b;
        case '/': return b === 0 ? UNKNOWN : a / b;
        case '%': return b === 0 ? UNKNOWN : a % b;
      }
    }
  }
  return UNKNOWN;
}

// ---------------------------------------------------------------------------
// restated-scenario
// ---------------------------------------------------------------------------

/**
 * A plain comparison of a counter with a literal, over one scenario, whose bound is exactly the extreme
 * value the counter reaches in that scenario's run: why, or null.
 * @param {Ctx} ctx @param {any} ev @param {string[]} scenarioIds @param {Set<string>} enabled
 */
function restatedScenario(ctx, ev, scenarioIds, enabled) {
  if (scenarioIds.length !== 1 || typeof ev.expr !== 'string') return null;
  const p = parseExpr(ev.expr);
  if (!p.ok || p.ast.t !== 'bin') return null;
  const flip = /** @type {Record<string, string>} */ ({ '<': '>', '<=': '>=', '>': '<', '>=': '<=' });
  let { op, a, b } = p.ast;
  if (!(op in flip)) return null;
  if (a.t === 'lit' && b.t === 'ref') { [a, b] = [b, a]; op = flip[op]; }
  if (a.t !== 'ref' || a.path.length !== 2 || b.t !== 'lit' || typeof b.v !== 'number') return null;
  const [behaviorId, name] = a.path;
  const d = domainOf(ctx, behaviorId, name, enabled);
  if (!d || d.t !== 'opaque' || entityOf(ctx, behaviorId, 'behavior')?.data.instances) return null;
  let trace;
  try { trace = ctx.runScenario(ctx.model, scenarioIds[0]); } catch { return null; }
  const valueAt = (/** @type {any} */ config) => config?.machines?.[behaviorId]?.vars?.[name];
  const values = [valueAt(trace?.initial), ...arr(trace?.steps).map((s) => valueAt(s?.config))].filter((v) => typeof v === 'number');
  if (values.length < 2) return null;
  const max = Math.max(...values);
  const min = Math.min(...values);
  if (max === min) return null;
  const bound = b.v;
  const tight = op === '<=' ? max === bound : op === '<' ? max + 1 === bound : op === '>=' ? min === bound : min - 1 === bound;
  if (!tight) return null;
  const extreme = op === '<=' || op === '<' ? `largest value is ${max}` : `smallest value is ${min}`;
  return `\`${ev.expr}\` bounds the counter "${behaviorId}.${name}" by exactly what its one scenario "${scenarioIds[0]}" produces (its ${extreme}): the bound restates the scenario rather than a rule that holds for other inputs.`;
}

// ---------------------------------------------------------------------------
// Grounding of behaviors
// ---------------------------------------------------------------------------

/**
 * @typedef {{anchored: boolean, binds: string[], reads: string[], free: string[], grounding: string}} BehaviorGrounding
 *   binds: what anchors the behavior directly; reads: the other behaviors its expressions read;
 *   free: payload fields of events that belong to no contract, read by a guard or an effect
 */

/** @param {Ctx} ctx @returns {Map<string, BehaviorGrounding>} */
function behaviorGroundings(ctx) {
  /** @type {Map<string, BehaviorGrounding>} */
  const out = new Map();
  const none = new Set();
  for (const b of ctx.model.byKind.behavior ?? []) {
    /** @type {string[]} */ const binds = [];
    /** @type {string[]} */ const reads = [];
    /** @type {string[]} */ const free = [];
    const refines = b.data.refines;
    if (typeof refines === 'string' && ctx.platform(refines) && entityOf(ctx, refines, 'behavior')) binds.push(`refines behavior "${refines}"`);
    for (const r of [b.data.storage?.record, b.data.instances?.storedIn]) {
      if (typeof r === 'string' && ctx.platform(r) && entityOf(ctx, r, 'record')) binds.push(`stored in record "${r}"`);
    }
    for (const t of (ctx.transitions.get(b.id) ?? []).filter((x) => nominal(x, none))) {
      const on = typeof t.data.on === 'string' ? t.data.on : null;
      const onContract = on ? contractOf(ctx, on) : null;
      if (on && onContract) binds.push(`reacts to event "${on}" of contract "${onContract}"${requiresText(ctx, onContract)}`);
      for (const fx of effectsOf(t)) {
        const e = emitsEvent(fx);
        const c = e ? contractOf(ctx, e) : null;
        if (e && c) binds.push(`emits event "${e}" of contract "${c}"${requiresText(ctx, c)}`);
      }
      for (const src of expressionsOf(t)) {
        const p = parseExpr(src);
        if (!p.ok) continue;
        for (const path of exprRefs(p.ast)) {
          if (path[0] === 'event' && path.length >= 2) {
            if (on && !onContract) free.push(`event "${on}" field "${path[1]}"`);
          } else if (path.length >= 2 && path[0] !== b.id && entityOf(ctx, path[0], 'behavior')) reads.push(path[0]);
        }
      }
    }
    out.set(b.id, { anchored: binds.length > 0, binds: uniq(binds), reads: uniq(reads), free: uniq(free), grounding: '' });
  }
  // A behavior that reads an anchored behavior is anchored through it.
  for (let changed = true; changed;) {
    changed = false;
    for (const [id, g] of out) {
      if (g.anchored) continue;
      const via = g.reads.filter((r) => out.get(r)?.anchored);
      if (via.length) {
        g.anchored = true;
        g.binds.push(...via.map((r) => `reads behavior "${r}"`));
        changed = true;
        void id;
      }
    }
  }
  for (const g of out.values()) g.grounding = !g.anchored ? 'self-contained' : g.free.length ? 'partly-bound' : 'bound';
  return out;
}

/** The contract of an event, when the platform has it. @param {Ctx} ctx @param {string} eventId */
function contractOf(ctx, eventId) {
  const c = entityOf(ctx, eventId, 'event')?.data.contract;
  return typeof c === 'string' && ctx.platform(c) && entityOf(ctx, c, 'contract') ? c : null;
}

/** @param {Ctx} ctx @param {string} contractId */
function requiresText(ctx, contractId) {
  const req = arr(entityOf(ctx, contractId, 'contract')?.data.auth?.requires).filter((x) => typeof x === 'string');
  return req.length ? `, which requires ${quoted(req)}` : '';
}

/** Every expression string of a transition: its guard, set values and payload values. @param {Entity} t */
function expressionsOf(t) {
  /** @type {string[]} */
  const out = [];
  if (typeof t.data.guard === 'string' && t.data.guard.trim()) out.push(t.data.guard);
  for (const fx of effectsOf(t)) {
    if (typeof fx.to === 'string') out.push(fx.to);
    if (fx.payload && typeof fx.payload === 'object') for (const v of Object.values(fx.payload)) if (typeof v === 'string') out.push(v);
  }
  return out;
}

/**
 * The grounding of a check that reads these behaviors.
 * @param {Ctx} ctx @param {string[]} behaviorIds
 * @returns {{grounding: string, why: string, reads: string[], free: string[]}}
 */
function combine(ctx, behaviorIds) {
  const gs = behaviorIds.map((id) => ({ id, g: ctx.behaviors.get(id) })).filter((x) => x.g);
  if (!gs.length) return { grounding: 'self-contained', why: 'The check reads no behavior that is anchored to the platform.', reads: [], free: [] };
  const reads = gs.map(({ id, g }) => `behavior "${id}" is ${g?.grounding}${g?.binds.length ? `: ${g.binds.join('; ')}` : ''}`);
  const free = uniq(gs.flatMap(({ g }) => g?.free ?? []));
  const all = (/** @type {string} */ s) => gs.every(({ g }) => g?.grounding === s);
  if (all('bound')) return { grounding: 'bound', why: `Every behavior the check reads is anchored to the platform and branches on no free input (${quoted(gs.map((x) => x.id))}).`, reads, free };
  if (all('self-contained')) {
    return { grounding: 'self-contained', why: `The behaviors the check reads (${quoted(gs.map((x) => x.id))}) refine nothing, are stored in no record, take no contract's events and read no anchored behavior${free.length ? `; they decide on payload fields the scenarios supply (${free.join(', ')})` : ''}.`, reads, free };
  }
  return { grounding: 'partly-bound', why: `Some of what the check reads is anchored to the platform and some is not${free.length ? `; free inputs: ${free.join(', ')}` : ''}.`, reads, free };
}

// ---------------------------------------------------------------------------
// Integrity rules
// ---------------------------------------------------------------------------

/** @param {Ctx} ctx @param {Entity} rule @returns {Strength} */
function ruleEntry(ctx, rule) {
  const check = 'integrity';
  const why = 'An integrity rule, evaluated over every entity of the specification on every edit.';
  const parsed = parseRule(String(rule.data.rule ?? ''));
  if (!parsed.ok) return { entity: 'integrityRule', check, grounding: 'not-applicable', details: { check: why, grounding: 'The rule does not parse, so it reads nothing.' } };
  /** @type {string[]} */ const kinds = [];
  /** @type {string[]} */ const literals = [];
  let any = false;
  const term = (/** @type {any} */ x) => {
    if (!x || typeof x !== 'object') return;
    if (x.t === 'lit') for (const k of x.vs) if (typeof k === 'string' && k.startsWith('s:')) literals.push(k.slice(2));
    if (x.of) term(x.of);
  };
  const walk = (/** @type {any} */ f) => {
    if (!f || typeof f !== 'object') return;
    if (f.t === 'all' || f.t === 'ex') {
      if (f.d.t === 'kinds') kinds.push(...f.d.ks);
      else if (f.d.t === 'any') any = true;
      else term(f.d.of);
      walk(f.f);
      walk(f.b);
      return;
    }
    if (f.f) walk(f.f);
    if (f.g) walk(f.g);
    if (f.a) term(f.a);
    if (f.b) term(f.b);
    for (const a of arr(f.args)) term(a);
  };
  walk(parsed.ast);
  const ks = uniq(kinds);
  const entities = any ? [...ctx.model.entities.values()] : ks.flatMap((k) => ctx.model.byKind[k] ?? []);
  const platform = entities.filter((e) => ctx.platform(e.id));
  const named = uniq(literals.filter((id) => ctx.model.entities.has(id)));
  const over = any ? 'every entity' : `every ${ks.join(', ')}`;
  const reads = [`${over} (${platform.length} of the platform's)`, ...named.map((id) => `names "${id}"`)];
  if (!platform.length) {
    return { entity: 'integrityRule', check, grounding: 'self-contained', details: { check: why, grounding: `Its quantifiers range over ${over}, and the platform has none: only entities the change adds are checked.`, reads } };
  }
  return { entity: 'integrityRule', check, grounding: 'bound', details: { check: why, grounding: `Quantifies over ${over} of the specification${named.length ? `, naming ${quoted(named)}` : ''}.`, reads } };
}
