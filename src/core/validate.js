// Semantic validation: rules that need the whole model rather than one value.
// Structural/type checks happen in parse.js. Severity meaning:
//   error   - the model is not well-formed; transactions producing errors are rejected
//   warning - well-formed but suspicious or unsupported (e.g. unknown claim method)
//   info    - a gap: something a complete specification is expected to state

import { parseExpr, exprRefs } from './expr.js';
import { CLAIM_METHODS } from './claim-methods.js';
import { own } from './own.js';
import { checkTaxonomy } from './interactions.js';
import { validateFaultModels } from './fault-model.js';
import { scenarioInputDiagnostics } from './scenario-input.js';
import { checkCodegenConsistency, exprClass, typeClass } from './codegen-model.js';
import { checkTypeShapes } from './type-shapes.js';
import { checkLanguages } from './language.js';
import { checkFunctions } from './function.js';
import { checkTenantData } from './tenant-data.js';
import { checkDerivations } from './derivation.js';
import { checkSuppliedInputs } from './supplied-inputs.js';
import { checkConstructConsistency } from './constructs.js';
import { checkUiConsistency } from './ui.js';
import { checkTelemetryConsistency } from './telemetry.js';

import { checkAccessConsistency } from './access.js';
import { checkCapabilityConsistency } from './capabilities.js';
import { checkResidency } from './residency.js';
import { allPoolMachines, checkPools, scenarioMachineIds, POOL_VARIABLES } from './pools.js';
import { READINESS_RULES } from './readiness.js';
import { notImplemented } from './realisation.js';
import { checkDataConsistency, dataRuleDiagnostics, RULE_IDS } from './data-model.js';
import { contractFields, contractErrorCodes } from './contract-trace.js';
import { parseType, typeAssignable, typeText } from './type-expr.js';
import { integrityDiagnostics } from './integrity.js';
import { minRuns, parseRational } from './metric-stats.js';
import { machineReadiness, keyFieldsOf } from './readiness-machines.js';
import { testRefProblem, describeTestRefProblem } from './evidence-ref.js';
import { LOGICAL, hierarchyOf, moduleDeclarations, cutMap, cutHierarchyId, isFacet } from './query.js';
import { portConnectionProblems, checkRealisations } from './abstraction.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

const VAR_RE = /^[A-Za-z_][A-Za-z0-9_]*$/;
const RESERVED_VARS = ['state', 'event', 'time', 'true', 'false', 'null'];

/**
 * `claimsOnly` runs only the checks of claims (parameters, scenarios, negatives, `models`): they read
 * what they can resolve and skip what they cannot, so they are safe on a model with unresolved references.
 * @param {Model} model @param {{claimsOnly?: boolean}} [opts]
 * @returns {Diagnostic[]}
 */
export function validateModel(model, opts = {}) {
  /** @type {Diagnostic[]} */
  const out = [];
  /**
   * @param {'error'|'warning'|'info'} severity @param {string} code @param {Entity} entity
   * @param {string} message @param {(string|number)[]} [sub]
   */
  const report = (severity, code, entity, message, sub) => {
    out.push({ code, severity, message, entityId: entity.id, loc: entity.loc, path: sub ? [...entity.path, ...sub] : entity.path });
  };
  const get = (/** @type {string} */ id) => model.entities.get(id);
  // The machines quota pools run as, by id (src/core/pools.js); claim expressions may read them.
  const poolMachines = allPoolMachines(model);
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];

  // --- components ---------------------------------------------------------
  // Any element may be the parent of others (composite is derived from having members); only cycles are wrong.
  for (const c of kind('component')) {
    const parentId = c.data.parent;
    if (typeof parentId === 'string') {
      const parent = get(parentId);
      const seen = new Set([c.id]);
      let cur = parent;
      while (cur && cur.kind === 'component') {
        if (seen.has(cur.id)) { report('error', 'component.parent-cycle', c, `Containment cycle through "${cur.id}".`, ['parent']); break; }
        seen.add(cur.id);
        cur = typeof cur.data.parent === 'string' ? get(cur.data.parent) : undefined;
      }
    }
  }

  // --- elements, hierarchies, facets and cuts ------------------------------
  if (!opts.claimsOnly) checkAbstraction(model, report);

  // --- relationships ------------------------------------------------------
  const relKeys = new Map();
  for (const r of kind('relationship')) {
    if (r.data.from === r.data.to) report('warning', 'relationship.self', r, 'Relationship connects an entity to itself.');
    const key = `${r.data.kind}|${r.data.from}|${r.data.to}`;
    if (relKeys.has(key)) report('warning', 'relationship.duplicate', r, `Same kind and endpoints as relationship "${relKeys.get(key)}".`);
    else relKeys.set(key, r.id);
  }
  // The interaction taxonomy: kinds without class, direction and parent, cycles in the kind tree, legacy kinds in use.
  checkTaxonomy(model, report);
  // Relationships that end at ports: requires to provides, one contract (abstraction.js).
  for (const p of portConnectionProblems(model)) {
    const r = get(p.relationship);
    if (r) report('error', p.code, r, p.message, p.path);
  }
  // Realisation maps between hierarchies: each path exists and runs from the source's placement to the target's.
  for (const m of checkRealisations(model)) {
    const e = get(m.id);
    if (!e) continue;
    for (const p of m.problems) report('error', p.code, e, p.message, p.path);
  }

  // --- behaviors, transitions --------------------------------------------
  /** @param {Entity} b @returns {Map<string, any>} */
  const varsOf = (b) => {
    const m = new Map();
    for (const v of Array.isArray(b.data.variables) ? b.data.variables : []) if (v && typeof v.name === 'string') m.set(v.name, v);
    return m;
  };

  /**
   * Check every reference in an expression against what is in scope.
   * @param {string} src @param {Entity} entity @param {(string|number)[]} sub
   * @param {{behavior?: Entity, event?: Entity, allowedBehaviors?: Set<string>}} scope
   */
  const checkExpr = (src, entity, sub, scope) => {
    const parsed = parseExpr(src);
    if (!parsed.ok) { report('error', 'expr.syntax', entity, `Expression "${src}": ${parsed.error.message} (at character ${parsed.error.pos + 1}).`, sub); return; }
    for (const path of exprRefs(parsed.ast)) {
      const text = path.join('.');
      if (path.length === 1) {
        if (path[0] === 'time') continue;
        if (scope.behavior && varsOf(scope.behavior).has(path[0])) continue;
        report('error', 'expr.reference', entity, `Expression "${src}": "${text}" is not a variable in scope.`, sub);
      } else if (path.length === 2 && path[0] === 'event') {
        if (!scope.event) { report('error', 'expr.reference', entity, `Expression "${src}": "event.*" is only available inside a transition.`, sub); continue; }
        const fields = Array.isArray(scope.event.data.payload) ? scope.event.data.payload.map((/** @type {any} */ f) => f?.name) : [];
        if (!fields.includes(path[1])) report('error', 'expr.reference', entity, `Expression "${src}": event "${scope.event.id}" declares no payload field "${path[1]}".`, sub);
      } else if (path.length === 2 && !get(path[0]) && poolMachines.has(path[0])) {
        // A machine a quota pool runs as (src/core/pools.js).
        if (scope.allowedBehaviors && !scope.allowedBehaviors.has(path[0])) { report('error', 'expr.reference', entity, `Expression "${src}": pool machine "${path[0]}" is not part of every listed scenario.`, sub); continue; }
        if (path[1] !== 'state' && !POOL_VARIABLES.includes(path[1])) report('error', 'expr.reference', entity, `Expression "${src}": pool machine "${path[0]}" has no variable "${path[1]}"; it has ${POOL_VARIABLES.join(', ')}.`, sub);
      } else if (path.length === 2) {
        const b = get(path[0]);
        if (!b || b.kind !== 'behavior') { report('error', 'expr.reference', entity, `Expression "${src}": "${path[0]}" is not a behavior.`, sub); continue; }
        if (scope.allowedBehaviors && !scope.allowedBehaviors.has(b.id)) { report('error', 'expr.reference', entity, `Expression "${src}": behavior "${b.id}" is not part of every listed scenario.`, sub); continue; }
        if (path[1] !== 'state' && !varsOf(b).has(path[1])) report('error', 'expr.reference', entity, `Expression "${src}": behavior "${b.id}" has no variable "${path[1]}".`, sub);
      } else {
        report('error', 'expr.reference', entity, `Expression "${src}": "${text}" is too deeply qualified.`, sub);
      }
    }
  };

  /**
   * A timer delay read at run time, {expr, simulate} (docs/model-and-format.md, "User interface, third set"):
   * only on an implementation-level machine; expr is an expression of a number over the machine's variables,
   * time and the event's payload, which generated code evaluates when the timer is set; simulate is the delay
   * the simulator uses (a number, a duration or a distribution), since a simulated run has no such value.
   * @param {any} fx @param {Entity} t @param {Entity} b @param {any} scope @param {(string|number)[]} sub
   */
  const checkTimerDelay = (fx, t, b, scope, sub) => {
    const at = [...sub, 'after'];
    const a = fx.after;
    const extra = Object.keys(a).filter((k) => k !== 'expr' && k !== 'simulate');
    if (extra.length) report('error', 'effect.after', t, `A timer delay read at run time is {expr, simulate}; ${extra.join(', ')} ${extra.length > 1 ? 'are' : 'is'} not part of it.`, at);
    if (b.data.level !== 'implementation') report('error', 'effect.after', t, `Timer "${fx.timer}" reads its delay at run time, which only an implementation-level machine may do; behavior "${b.id}" is not one.`, at);
    const sim = a.simulate;
    if (!((typeof sim === 'number' && sim >= 0) || typeof sim === 'string' || (sim && typeof sim === 'object' && !Array.isArray(sim)))) report('error', 'effect.after', t, `Timer "${fx.timer}" reads its delay at run time and needs "simulate", the delay a simulated run uses (a non-negative number, a duration or a distribution).`, at);
    if (typeof a.expr !== 'string') { report('error', 'effect.after', t, `The run-time delay of timer "${fx.timer}" is an expression (a string).`, [...at, 'expr']); return; }
    checkExpr(a.expr, t, [...at, 'expr'], scope);
    const parsed = parseExpr(a.expr);
    if (!parsed.ok) return;
    const vars = varsOf(b);
    const payload = new Map((Array.isArray(scope.event?.data.payload) ? scope.event.data.payload : []).filter((/** @type {any} */ f) => f && typeof f.name === 'string').map((/** @type {any} */ f) => [f.name, f.type]));
    const VAR_CLASS = { number: 'number', boolean: 'bool', string: 'string' };
    const r = exprClass(parsed.ast, (path) => {
      if (path.length === 1 && path[0] === 'time') return 'number';
      if (path.length === 1) return /** @type {any} */ (VAR_CLASS)[vars.get(path[0])?.type] ?? 'any';
      if (path.length === 2 && path[0] === 'event') return payload.has(path[1]) ? typeClass(model, payload.get(path[1])) : 'any';
      return 'any';
    });
    const complaint = r.error ?? (r.cls === 'number' || r.cls === 'any' ? undefined : `it is a ${r.cls}, and a delay is a number`);
    if (complaint) report('error', 'effect.after', t, `The run-time delay "${a.expr}" of timer "${fx.timer}": ${complaint}.`, [...at, 'expr']);
  };

  /**
   * The `models` property of a claim links a check over the behavior model to the requirement it restates:
   * it must name requirements (claims of kind requirement). An id that resolves to nothing is reported by the parser.
   * @param {Entity} c
   */
  const checkModels = (c) => {
    const v = c.data.models;
    if (v === undefined) return;
    (Array.isArray(v) ? v : [v]).forEach((/** @type {any} */ id, /** @type {number} */ i) => {
      if (typeof id !== 'string') return;
      const t = get(id);
      if (t && (t.kind !== 'claim' || t.data.kind !== 'requirement')) {
        report('error', 'claim.models-not-requirement', c, `"models" names "${id}", which is not a requirement (a claim of kind "requirement").`, Array.isArray(v) ? ['models', i] : ['models']);
      }
    });
  };

  /**
   * An implementation behavior that refines a model behavior (docs/claims-and-evidence.md, "Refinement"):
   * one level only, and a mapping that names every state and transition of the implementation and every
   * variable of the model, with nothing unknown on either side. A `refines` that names something other than
   * a behavior is reported by the parser (ref.kind, ref.unresolved).
   * @param {Entity} b
   */
  const checkRefinement = (b) => {
    const refines = b.data.refines;
    const map = b.data.refinement;
    if (refines === undefined) {
      if (map !== undefined) report('error', 'behavior.refinement-without-refines', b, `Behavior "${b.id}" declares a refinement mapping but does not name the behavior it refines ("refines").`, ['refinement']);
      return;
    }
    if (b.data.level !== 'implementation') report('error', 'behavior.refines-model-level', b, `Behavior "${b.id}" is a model-level machine (level ${b.data.level === undefined ? 'absent, so model' : `"${b.data.level}"`}); only a machine with level "implementation" refines another.`, ['refines']);
    const A = typeof refines === 'string' ? get(refines) : undefined;
    if (!A || A.kind !== 'behavior') return;
    if (A.data.refines !== undefined) report('error', 'behavior.refines-chain', b, `Behavior "${b.id}" refines "${A.id}", which itself refines "${A.data.refines}"; refinement has one level, from an implementation machine to a model machine.`, ['refines']);
    if (!map || typeof map !== 'object' || Array.isArray(map)) { report('error', 'behavior.refinement-missing', b, `Behavior "${b.id}" refines "${A.id}" but declares no refinement mapping ("refinement": {states, variables, transitions}).`, ['refines']); return; }
    const obj = (/** @type {any} */ v) => (v && typeof v === 'object' && !Array.isArray(v) ? v : {});
    const states = obj(map.states), variables = obj(map.variables), transitions = obj(map.transitions);
    if (map.timeScale !== undefined && !(typeof map.timeScale === 'number' && Number.isFinite(map.timeScale) && map.timeScale > 0)) {
      report('error', 'refinement.time-scale', b, `The refinement's timeScale must be a positive number (implementation time units per model tick), not ${JSON.stringify(map.timeScale)}.`, ['refinement', 'timeScale']);
    }
    const iStates = kind('state').filter((s) => s.owner === b.id).map((s) => s.id);
    const aStates = kind('state').filter((s) => s.owner === A.id).map((s) => s.id);
    const iTrans = kind('transition').filter((t) => t.owner === b.id).map((t) => t.id);
    const aTrans = kind('transition').filter((t) => t.owner === A.id).map((t) => t.id);
    const iVars = varsOf(b), aVars = varsOf(A);
    for (const [k, v] of Object.entries(states)) {
      if (!iStates.includes(k)) report('error', 'refinement.unknown-state', b, `The refinement maps "${k}", which is not a state of "${b.id}".`, ['refinement', 'states', k]);
      if (typeof v !== 'string' || !aStates.includes(v)) report('error', 'refinement.unknown-state', b, `The refinement maps state "${k}" to ${JSON.stringify(v)}, which is not a state of "${A.id}".`, ['refinement', 'states', k]);
    }
    for (const s of iStates) if (!Object.hasOwn(states, s)) report('error', 'refinement.unmapped-state', b, `State "${s}" of "${b.id}" is missing from the refinement's states.`, ['refinement', 'states']);
    for (const [k, v] of Object.entries(transitions)) {
      if (!iTrans.includes(k)) report('error', 'refinement.unknown-transition', b, `The refinement maps "${k}", which is not a transition of "${b.id}".`, ['refinement', 'transitions', k]);
      if (v !== null && (typeof v !== 'string' || !aTrans.includes(v))) report('error', 'refinement.unknown-transition', b, `The refinement maps transition "${k}" to ${JSON.stringify(v)}, which is neither a transition of "${A.id}" nor null (a stutter).`, ['refinement', 'transitions', k]);
    }
    for (const t of iTrans) if (!Object.hasOwn(transitions, t)) report('error', 'refinement.unmapped-transition', b, `Transition "${t}" of "${b.id}" is missing from the refinement's transitions (map it to a transition of "${A.id}" or to null).`, ['refinement', 'transitions']);
    for (const [k, v] of Object.entries(variables)) {
      const sub = ['refinement', 'variables', k];
      if (!aVars.has(k)) report('error', 'refinement.unknown-variable', b, `The refinement maps "${k}", which is not a variable of "${A.id}".`, sub);
      if (typeof v !== 'string') { report('error', 'refinement.expr', b, `The mapping of "${k}" must be an expression string over the variables of "${b.id}".`, sub); continue; }
      const parsed = parseExpr(v);
      if (!parsed.ok) { report('error', 'refinement.expr', b, `The mapping of "${k}", "${v}": ${parsed.error.message} (at character ${parsed.error.pos + 1}).`, sub); continue; }
      for (const path of exprRefs(parsed.ast)) {
        if (path.length !== 1 || !iVars.has(path[0])) report('error', 'refinement.unknown-variable', b, `The mapping of "${k}", "${v}": "${path.join('.')}" is not a variable of "${b.id}".`, sub);
      }
    }
    for (const name of aVars.keys()) if (!Object.hasOwn(variables, name)) report('error', 'refinement.unmapped-variable', b, `Variable "${name}" of "${A.id}" is missing from the refinement's variables.`, ['refinement', 'variables']);
  };

  // --- claims -------------------------------------------------------------
  // A closure so that it can also run alone (see `claimsOnly`).
  const claimChecks = () => {
  for (const c of kind('claim')) {
    checkModels(c);
    const ev = c.data.evaluate;
    if (!ev || typeof ev !== 'object') continue;
    if (typeof ev.method !== 'string') { report('error', 'claim.method.missing', c, 'Claim "evaluate" needs a string "method".', ['evaluate']); continue; }
    if (own(model.meta.verificationMethods, ev.method)) {
      // Carried out outside Exegra: nothing to check here beyond the method name.
      for (const k of Object.keys(ev)) if (k !== 'method') report('error', 'claim.param.unknown', c, `Verification method "${ev.method}" is external and takes no parameters.`, ['evaluate', k]);
      continue;
    }
    const mdef = own(/** @type {any} */ (CLAIM_METHODS), ev.method);
    if (!mdef) { report('warning', 'claim.method.unsupported', c, `Evaluation method "${ev.method}" is not supported by this build; the claim stays not evaluated.`, ['evaluate', 'method']); continue; }
    if (!mdef.kinds.includes(c.data.kind)) report('error', 'claim.method.kind', c, `Method "${ev.method}" evaluates ${mdef.kinds.join('/')} claims, not ${c.data.kind} claims.`, ['evaluate', 'method']);
    for (const k of Object.keys(ev)) if (k !== 'method' && !own(mdef.params, k)) report('error', 'claim.param.unknown', c, `Method "${ev.method}" has no parameter "${k}".`, ['evaluate', k]);
    if (ev.method === 'metric-bound') {
      // A metric claim with fewer runs than can ever hold (docs/simulation.md, "Claims over metrics").
      try {
        const need = minRuns(parseRational(ev.fraction ?? '0.95'), parseRational(ev.confidence ?? '0.95'));
        const runs = Number(ev.runs ?? 59);
        if (!(runs >= need)) report('error', 'claim.metric.runs', c, `Claim "${c.id}" can never hold with ${runs} runs; at least ${need} are needed at fraction ${ev.fraction ?? '0.95'} and confidence ${ev.confidence ?? '0.95'}.`, ['evaluate', 'runs']);
      } catch (e) {
        report('error', 'claim.param.value', c, `Claim "${c.id}": ${/** @type {Error} */ (e).message}`, ['evaluate']);
      }
      if ((ev.op === undefined) === (ev.approx === undefined)) report('error', 'claim.param.value', c, 'A metric-bound claim needs either "op" and "bound" or "approx".', ['evaluate']);
    }
    /** @type {Set<string>|undefined} */
    let allowedBehaviors;
    if (Array.isArray(ev.scenarios)) {
      for (const sid of ev.scenarios) {
        const sc = get(sid);
        if (!sc || sc.kind !== 'scenario') continue;
        const set = scenarioMachineIds(model, sc);
        allowedBehaviors = allowedBehaviors ? new Set([...allowedBehaviors].filter((x) => set.has(x))) : set;
      }
      if (!ev.scenarios.length) report('error', 'claim.param.value', c, 'At least one scenario is required.', ['evaluate', 'scenarios']);
    }
    for (const [name, pdefRaw] of Object.entries(mdef.params)) {
      const pdef = /** @type {any} */ (pdefRaw);
      const v = ev[name];
      const sub = ['evaluate', name];
      if (v === undefined) { if (pdef.required) report('error', 'claim.param.required', c, `Method "${ev.method}" needs parameter "${name}".`, ['evaluate']); continue; }
      const type = pdef.type;
      if (type === 'selector') {
        const okIds = typeof v === 'string' || (Array.isArray(v) && v.every((x) => typeof x === 'string'));
        if (!okIds) {
          if (!v || typeof v !== 'object' || Array.isArray(v)) { report('error', 'claim.param.type', c, `Parameter "${name}" must be a selector.`, sub); continue; }
          for (const k of Object.keys(v)) if (!['ids', 'category', 'kind', 'tag', 'facet', 'trustZone', 'within', 'outside', 'except', 'all'].includes(k)) report('error', 'claim.selector.unknown', c, `Unsupported selector field "${k}".`, [...sub, k]);
          if (v.outside !== undefined) {
            const o = typeof v.outside === 'string' ? get(v.outside) : undefined;
            if (!o || (o.kind !== 'component' && o.kind !== 'system')) report('error', 'claim.selector.outside', c, `Selector "${name}" takes the complement of ${JSON.stringify(v.outside)}, which is not an element.`, [...sub, 'outside']);
          }
          if (v.except !== undefined) {
            if (!Array.isArray(v.except)) report('error', 'claim.selector.except', c, `Selector "${name}": "except" must be a list of {"id": element, "reason": text}.`, [...sub, 'except']);
            else v.except.forEach((/** @type {any} */ x, /** @type {number} */ i) => {
              if (!x || typeof x !== 'object' || Array.isArray(x) || typeof x.id !== 'string' || typeof x.reason !== 'string' || !x.reason.trim() || Object.keys(x).some((k) => k !== 'id' && k !== 'reason')) {
                report('error', 'claim.selector.except', c, `Selector "${name}": exception ${i} must be {"id": element, "reason": text}; an element is left out of a selection only with a stated reason.`, [...sub, 'except', i]);
              } else if (get(x.id)?.kind !== 'component') report('error', 'claim.selector.except', c, `Selector "${name}" leaves out "${x.id}", which is not a component.`, [...sub, 'except', i, 'id']);
            });
          }
          if (v.facet !== undefined && (typeof v.facet !== 'string' || !isFacet(model, v.facet))) report('error', 'claim.selector.facet', c, `Selector "${name}" names facet ${JSON.stringify(v.facet)}, which is neither a declared facet nor a tag of any component.`, [...sub, 'facet']);
          if (!Object.keys(v).length) report('error', 'claim.selector.empty', c, `Selector "${name}" selects nothing; use {"all": true} to select every component.`, sub);
        }
      } else if (type === 'string') { if (typeof v !== 'string') report('error', 'claim.param.type', c, `Parameter "${name}" must be a string.`, sub); }
      else if (type === 'strings') { if (!(Array.isArray(v) && v.every((x) => typeof x === 'string'))) report('error', 'claim.param.type', c, `Parameter "${name}" must be an array of strings.`, sub); }
      else if (type === 'edge-filter') {
        const ok = v && typeof v === 'object' && !Array.isArray(v) && typeof v.property === 'string' && Array.isArray(v.values) && v.values.length > 0 && v.values.every((/** @type {any} */ x) => typeof x === 'string') && Object.keys(v).every((k) => k === 'property' || k === 'values');
        if (!ok) report('error', 'claim.param.type', c, `Parameter "${name}" must be {"property": name, "values": [one or more strings]}.`, sub);
      }
      else if (type === 'boolean') { if (typeof v !== 'boolean') report('error', 'claim.param.type', c, `Parameter "${name}" must be true or false.`, sub); }
      else if (type === 'expr') { if (typeof v !== 'string') report('error', 'claim.param.type', c, `Parameter "${name}" must be an expression string.`, sub); else checkExpr(v, c, sub, { allowedBehaviors }); }
      else if (type === 'matcher') {
        const ok = v && typeof v === 'object' && !Array.isArray(v) && Object.keys(v).length === 1 && (typeof v.event === 'string' || typeof v.transition === 'string');
        if (!ok) report('error', 'claim.param.type', c, `Parameter "${name}" must be {"event": id} or {"transition": id}.`, sub);
      } else if (type === 'negatives') {
        if (!Array.isArray(v)) { report('error', 'claim.param.type', c, `Parameter "${name}" must be an array of {"scenario": id, "faults": [ids]}.`, sub); continue; }
        const listed = Array.isArray(ev.scenarios) ? ev.scenarios : typeof ev.scenarios === 'string' ? [ev.scenarios] : [];
        v.forEach((/** @type {any} */ neg, /** @type {number} */ i) => {
          const at = [...sub, i];
          if (!neg || typeof neg !== 'object' || Array.isArray(neg)) { report('error', 'claim.negative.type', c, `Negative ${i} must be {"scenario": id, "faults": [ids]}.`, at); return; }
          for (const k of Object.keys(neg)) if (k !== 'scenario' && k !== 'faults' && k !== 'note') report('error', 'claim.negative.unknown', c, `Negative ${i} has no field "${k}" (fields: scenario, faults, note).`, [...at, k]);
          if (typeof neg.scenario !== 'string') report('error', 'claim.negative.scenario', c, `Negative ${i} needs a "scenario".`, at);
          else if (!listed.includes(neg.scenario)) report('error', 'claim.negative.scenario', c, `Negative ${i} runs "${neg.scenario}", which is not one of the claim's scenarios; a negative is a listed scenario with extra faults.`, [...at, 'scenario']);
          if (!Array.isArray(neg.faults) || !neg.faults.length || !neg.faults.every((/** @type {any} */ x) => typeof x === 'string')) {
            report('error', 'claim.negative.faults', c, `Negative ${i} needs a non-empty "faults" list: a negative removes a protection by injecting at least one fault.`, [...at, 'faults']);
            return;
          }
          const sc = typeof neg.scenario === 'string' ? get(neg.scenario) : undefined;
          const active = sc && sc.kind === 'scenario' && Array.isArray(sc.data.faults) ? sc.data.faults : [];
          neg.faults.forEach((/** @type {string} */ fid, /** @type {number} */ j) => {
            if (active.includes(fid)) report('error', 'claim.negative.faults', c, `Negative ${i}: scenario "${neg.scenario}" already activates fault "${fid}", so adding it changes nothing.`, [...at, 'faults', j]);
            // A fault that enables or disables a transition of a behavior the scenario does not run changes nothing there.
            const fd = get(fid);
            const target = fd && fd.kind === 'fault' && (fd.data.kind === 'enable-transition' || fd.data.kind === 'disable-transition') ? get(fd.data.transition) : undefined;
            if (target && target.kind === 'transition' && sc && sc.kind === 'scenario' && !(Array.isArray(sc.data.behaviors) ? sc.data.behaviors : []).includes(target.owner)) {
              report('warning', 'claim.negative.fault-inert', c, `Negative ${i}: fault "${fid}" targets transition "${target.id}" of behavior "${target.owner}", which scenario "${neg.scenario}" does not run, so it changes nothing there.`, [...at, 'faults', j]);
            }
          });
          if (neg.note !== undefined && typeof neg.note !== 'string') report('error', 'claim.negative.type', c, `Negative ${i}: "note" must be a string.`, [...at, 'note']);
        });
      } else if (type.startsWith('ids:')) {
        if (!(typeof v === 'string' || (Array.isArray(v) && v.every((x) => typeof x === 'string')))) report('error', 'claim.param.type', c, `Parameter "${name}" must be an id or an array of ids.`, sub);
      }
    }
    if (ev.method === 'data-model' && Array.isArray(ev.rules)) {
      ev.rules.forEach((/** @type {any} */ r, /** @type {number} */ i) => { if (!RULE_IDS.includes(r)) report('error', 'claim.param.value', c, `Unknown data rule "${r}"; the rules are ${RULE_IDS.join(', ')}.`, ['evaluate', 'rules', i]); });
      if (!ev.rules.length) report('error', 'claim.param.value', c, 'At least one data rule is required.', ['evaluate', 'rules']);
    }
    if (ev.method === 'refines' && ev.behavior !== undefined) {
      const b = typeof ev.behavior === 'string' ? get(ev.behavior) : undefined;
      if (typeof ev.behavior !== 'string') report('error', 'claim.param.value', c, 'Method "refines" takes one behavior id in "behavior".', ['evaluate', 'behavior']);
      else if (b && b.kind === 'behavior' && b.data.refines === undefined) report('error', 'claim.param.value', c, `Behavior "${b.id}" declares no "refines", so there is no refinement to check.`, ['evaluate', 'behavior']);
      if (b && b.kind === 'behavior') {
        (Array.isArray(ev.scenarios) ? ev.scenarios : []).forEach((/** @type {any} */ sid, /** @type {number} */ i) => {
          const sc = typeof sid === 'string' ? get(sid) : undefined;
          if (sc && sc.kind === 'scenario' && !(Array.isArray(sc.data.behaviors) && sc.data.behaviors.includes(b.id))) report('error', 'claim.param.value', c, `Scenario "${sc.id}" does not run behavior "${b.id}".`, ['evaluate', 'scenarios', i]);
        });
      }
    }
    if (ev.method === 'eventually' && ev.occurs === undefined && ev.expr === undefined) report('error', 'claim.param.required', c, 'Method "eventually" needs "occurs" or "expr".', ['evaluate']);
  }
  };

  if (opts.claimsOnly) { claimChecks(); return out; }

  /**
   * The durability of a machine (NC-7): `record` (default) names the record that holds it; `memory` lives in process
   * memory for a connection or tab, so it names no record and creates none.
   * @param {Entity} b
   */
  function checkStorageDurability(b) {
    const st = b.data.storage;
    if (!st || typeof st !== 'object' || Array.isArray(st)) return;
    if (st.durability === 'memory') {
      for (const k of ['record', 'key', 'fields', 'state', 'stateValues']) {
        if (st[k] !== undefined) report('error', 'storage.durability', b, `Behavior "${b.id}" has storage.durability "memory", so it is held in no record, but declares storage.${k}.`, ['storage', k]);
      }
      if (st.creates === true) report('error', 'storage.durability', b, `Behavior "${b.id}" has storage.durability "memory" and storage.creates true: a machine in memory creates no records.`, ['storage', 'creates']);
      const inst = b.data.instances;
      if (inst && typeof inst === 'object' && inst.storedIn !== undefined) report('error', 'storage.durability', b, `Behavior "${b.id}" has storage.durability "memory" but instances.storedIn names a record.`, ['instances', 'storedIn']);
      if (b.data.transaction !== undefined) report('error', 'storage.durability', b, `Behavior "${b.id}" has storage.durability "memory" but declares a transaction, which only a record gives.`, ['transaction']);
    } else {
      for (const k of ['record', 'key']) {
        if (k === 'key' ? !keyFieldsOf(st[k]) : typeof st[k] !== 'string') report('error', 'storage.durability', b, `Behavior "${b.id}" has storage.durability "${st.durability ?? 'record'}" (default record) and so needs storage.${k}.`, ['storage', k]);
      }
    }
  }

  // Realisation (NC-6): a machine or contract explicitly shipped must not follow a component that is not implemented.
  for (const b of kind('behavior')) {
    if (b.data.realisation === 'shipped' && notImplemented(model, b)) report('error', 'behavior.realisation-subject', b, `Behavior "${b.id}" is declared realisation "shipped", but its subject "${b.data.subject}" has implementation.status "not-implemented"; declare "target", or leave it out for the default.`, ['realisation']);
  }
  for (const c of kind('contract')) {
    if (c.data.deployment === 'shipped' && notImplemented(model, c)) report('error', 'contract.deployment-subject', c, `Contract "${c.id}" is declared deployment "shipped", but implementedBy "${c.data.implementedBy}" has implementation.status "not-implemented"; declare "target", or leave it out for the default.`, ['deployment']);
  }

  for (const b of kind('behavior')) {
    checkStorageDurability(b);
    const initial = get(b.data.initial);
    if (initial && initial.kind === 'state' && initial.owner !== b.id) report('error', 'behavior.initial-foreign', b, `Initial state "${initial.id}" belongs to behavior "${initial.owner}".`, ['initial']);
    const names = new Set();
    (Array.isArray(b.data.variables) ? b.data.variables : []).forEach((/** @type {any} */ v, /** @type {number} */ i) => {
      if (!v || typeof v.name !== 'string') return;
      if (!VAR_RE.test(v.name) || RESERVED_VARS.includes(v.name)) report('error', 'behavior.variable-name', b, `Variable name "${v.name}" must be a plain identifier and not a reserved word.`, ['variables', i]);
      if (names.has(v.name)) report('error', 'behavior.variable-duplicate', b, `Variable "${v.name}" is declared twice.`, ['variables', i]);
      names.add(v.name);
      if (['boolean', 'number', 'string'].includes(v.type) && typeof v.initial !== v.type) report('error', 'behavior.variable-initial', b, `Variable "${v.name}" is declared ${v.type} but its initial value is ${JSON.stringify(v.initial)}.`, ['variables', i]);
    });
    // reachability of states from the initial state (ignoring guards)
    const states = kind('state').filter((s) => s.owner === b.id);
    const transitions = kind('transition').filter((t) => t.owner === b.id);
    // The engine takes the first enabled transition in declaration order: two unguarded transitions on one event
    // and state leave the order alone to decide which fires.
    /** @type {Map<string, Entity>} */
    const firstUnguarded = new Map();
    for (const t of transitions) {
      if (t.data.faultOnly === true || (typeof t.data.guard === 'string' && t.data.guard.trim() !== '')) continue;
      const key = `${t.data.from}\u0000${t.data.on}`;
      const earlier = firstUnguarded.get(key);
      if (earlier) report('warning', 'transition.order-decides', t, `Transitions "${earlier.id}" and "${t.id}" are both unguarded on event "${t.data.on}" in state "${t.data.from}": only declaration order decides which fires, and "${t.id}" can fire only while "${earlier.id}" is disabled. Add a guard to one of them.`);
      else firstUnguarded.set(key, t);
    }
    const reach = new Set([b.data.initial]);
    let grew = true;
    while (grew) {
      grew = false;
      for (const t of transitions) if (reach.has(t.data.from) && !reach.has(t.data.to)) { reach.add(t.data.to); grew = true; }
    }
    for (const s of states) if (!reach.has(s.id)) report('warning', 'behavior.unreachable-state', s, `State "${s.id}" cannot be reached from the initial state of "${b.id}".`);
    checkRefinement(b);
  }

  for (const t of kind('transition')) {
    const b = t.owner ? get(t.owner) : undefined;
    if (!b) continue;
    for (const end of ['from', 'to']) {
      const s = get(t.data[end]);
      if (s && s.kind === 'state' && s.owner !== b.id) report('error', 'transition.foreign-state', t, `State "${s.id}" belongs to behavior "${s.owner}", not "${b.id}".`, [end]);
    }
    const ev = get(t.data.on);
    const scope = { behavior: b, event: ev && ev.kind === 'event' ? ev : undefined };
    if (typeof t.data.guard === 'string') checkExpr(t.data.guard, t, ['guard'], scope);
    (Array.isArray(t.data.effects) ? t.data.effects : []).forEach((/** @type {any} */ fx, /** @type {number} */ i) => {
      if (!fx || typeof fx !== 'object') return;
      const sub = ['effects', i];
      const keys = Object.keys(fx);
      if ('set' in fx) {
        for (const k of keys) if (!['set', 'to'].includes(k)) report('error', 'effect.unknown', t, `Unsupported field "${k}" in a "set" effect.`, sub);
        const v = varsOf(b).get(fx.set);
        if (!v) { report('error', 'effect.variable', t, `Effect sets "${fx.set}", which is not a variable of behavior "${b.id}".`, sub); return; }
        if (!('to' in fx)) report('error', 'effect.value', t, `Effect on "${fx.set}" needs a "to" value.`, sub);
        else if (typeof fx.to === 'string') checkExpr(fx.to, t, [...sub, 'to'], scope);
        else if (fx.to && typeof fx.to === 'object' && 'sample' in fx.to) { /* format 2: a sampled number */ }
        else if (typeof fx.to !== v.type) report('error', 'effect.value', t, `Effect sets ${v.type} variable "${fx.set}" to ${JSON.stringify(fx.to)}.`, sub);
      } else if ('timer' in fx) {
        // Format 2 (docs/simulation.md, "Latency, timeouts and timers").
        for (const k of keys) if (!['timer', 'after', 'emit', 'payload'].includes(k)) report('error', 'effect.unknown', t, `Unsupported field "${k}" in a "timer" effect.`, sub);
        if (typeof fx.timer !== 'string') report('error', 'effect.timer', t, 'Effect "timer" must be a timer name.', sub);
        const e = get(fx.emit);
        if (!e || e.kind !== 'event') report('error', 'effect.emit', t, `Timer "${fx.timer}" emits "${fx.emit}", which is not an event.`, sub);
        if (fx.after === undefined) report('error', 'effect.after', t, `Timer "${fx.timer}" needs "after".`, sub);
        else if (fx.after && typeof fx.after === 'object' && !Array.isArray(fx.after) && 'expr' in fx.after) checkTimerDelay(fx, t, b, scope, sub);
      } else if ('cancel' in fx) {
        for (const k of keys) if (k !== 'cancel') report('error', 'effect.unknown', t, `Unsupported field "${k}" in a "cancel" effect.`, sub);
      } else if ('use' in fx || 'acquire' in fx || 'release' in fx) {
        // Format 2 (docs/simulation.md, "Resources").
        const verb = 'use' in fx ? 'use' : 'acquire' in fx ? 'acquire' : 'release';
        const allowed = verb === 'release' ? ['release', 'class', 'units'] : [verb, 'class', 'units', 'then', 'refused', 'payload', ...(verb === 'use' ? ['demand'] : [])];
        for (const k of keys) if (!allowed.includes(k)) report('error', 'effect.unknown', t, `Unsupported field "${k}" in a "${verb}" effect.`, sub);
        const r = get(fx[verb]);
        if (!r || r.kind !== 'resource') { report('error', 'effect.resource', t, `Effect ${verb}s "${fx[verb]}", which is not a resource.`, sub); return; }
        const classes = Array.isArray(r.data.classes) ? r.data.classes : [];
        if (fx.class !== undefined && !classes.some((/** @type {any} */ c) => c?.id === fx.class)) report('error', 'effect.class', t, `Resource "${r.id}" has no class "${fx.class}".`, sub);
        if (fx.class === undefined && classes.length > 1) report('error', 'effect.class', t, `Effect on "${r.id}" must name one of its classes.`, sub);
        for (const k of ['then', 'refused']) {
          if (fx[k] === undefined) continue;
          const e = get(fx[k]);
          if (!e || e.kind !== 'event') report('error', 'effect.emit', t, `Effect "${k}" names "${fx[k]}", which is not an event.`, sub);
        }
        if (verb !== 'release' && fx.then === undefined) report('error', 'effect.then', t, `A "${verb}" effect needs "then".`, sub);
        if (verb === 'use' && fx.demand === undefined) report('error', 'effect.demand', t, 'A "use" effect needs "demand".', sub);
      } else if ('emit' in fx) {
        for (const k of keys) if (!['emit', 'after', 'payload', 'target', 'via', 'size', 'fanout', 'to'].includes(k)) report('error', 'effect.unknown', t, `Unsupported field "${k}" in an "emit" effect.`, sub);
        if (typeof fx.emit !== 'string') report('error', 'effect.emit', t, 'Effect "emit" must be an event id.', sub);
        if ('via' in fx) {
          const l = get(fx.via);
          if (!l || l.kind !== 'link') report('error', 'effect.via', t, `Effect sends over "${fx.via}", which is not a link.`, sub);
          if ('after' in fx) report('error', 'effect.after', t, 'An emit with "via" cannot also have "after".', sub);
        }
        if ('to' in fx) {
          const rcv = typeof fx.to === 'string' ? get(fx.to) : undefined;
          if (!rcv || (rcv.kind !== 'component' && rcv.kind !== 'contract')) report('error', 'effect.to', t, `Effect "to" must name a component or a contract; "${fx.to}" is neither.`, sub);
        }
        if ('target' in fx && fx.target !== 'reply') report('error', 'effect.target', t, 'Effect "target" must be "reply".', sub);
        if ('after' in fx && !(typeof fx.after === 'number' && fx.after >= 0) && !(typeof fx.after === 'string' || (fx.after && typeof fx.after === 'object'))) report('error', 'effect.after', t, 'Effect "after" must be a non-negative number of logical ticks, a duration or a distribution.', sub);
        if ('payload' in fx) {
          if (!fx.payload || typeof fx.payload !== 'object' || Array.isArray(fx.payload)) report('error', 'effect.payload', t, 'Effect "payload" must be an object.', sub);
          else for (const [k, v] of Object.entries(fx.payload)) if (typeof v === 'string') checkExpr(v, t, [...sub, 'payload', k], scope);
        }
      } else {
        report('error', 'effect.unknown', t, 'An effect must be {"set": variable, "to": value}, {"emit": event}, or (format 2) a use, acquire, release, timer or cancel effect.', sub);
      }
    });
  }

  // --- implementation-level machines (src/core/readiness-machines.js) ---------
  out.push(...machineReadiness(model));

  // --- contract events ----------------------------------------------------
  // An unknown contract is reported by the parser (ref.unresolved, ref.kind) with its position.
  for (const ev of kind('event')) {
    const d = ev.data;
    const contract = typeof d.contract === 'string' ? get(d.contract) : undefined;
    if (d.contract === undefined) {
      if (d.role !== undefined) report('error', 'event.role-without-contract', ev, 'An event with a role must name its contract.', ['role']);
      if (d.correlation !== undefined) report('error', 'event.correlation-without-contract', ev, 'An event with a correlation field must name its contract.', ['correlation']);
      continue;
    }
    if (!contract || contract.kind !== 'contract') continue;
    const role = d.role;
    if (role !== 'request' && role !== 'response' && role !== 'error') {
      if (role === undefined) report('error', 'event.role-missing', ev, `Event "${ev.id}" names contract "${contract.id}" but no role (request, response or error).`, ['contract']);
      continue;
    }
    const payload = (Array.isArray(d.payload) ? d.payload : []).map((/** @type {any} */ f, /** @type {number} */ i) => ({ f, i })).filter(({ f }) => f && typeof f.name === 'string');
    const names = new Set(payload.map(({ f }) => f.name));
    const fields = contractFields(contract, role);
    if (role !== 'error') {
      const what = role === 'request' ? 'an input' : 'an output';
      for (const { f, i } of payload) {
        const def = fields.get(f.name);
        if (!def) { report('error', 'event.contract-field', ev, `Payload field "${f.name}" is not ${what} of contract "${contract.id}".`, ['payload', i]); continue; }
        const from = parseType(f.type), to = parseType(def.type);
        if (!typeAssignable(from, to)) report('error', 'event.contract-type', ev, `Payload field "${f.name}" is ${typeText(from)}, but contract "${contract.id}" declares ${typeText(to)}.`, ['payload', i, 'type']);
      }
      if (role === 'request') for (const [k, def] of fields) if (!def.optional && !names.has(k)) report('error', 'event.contract-missing', ev, `Request event "${ev.id}" does not carry input "${k}" of contract "${contract.id}" (mark the input "optional": true if it may be left out).`, ['payload']);
    } else {
      const code = payload.find(({ f }) => f.name === 'code');
      if (!code) report('error', 'event.error-code', ev, `Error event "${ev.id}" needs a payload field "code".`, ['payload']);
      else {
        const codes = contractErrorCodes(contract);
        for (const a of parseType(code.f.type)) if (a.k === 'lit' && typeof a.v === 'string' && !codes.includes(a.v)) report('error', 'event.error-code', ev, `Error code "${a.v}" is not among the errors of contract "${contract.id}" (${codes.join(', ') || 'none declared'}).`, ['payload', code.i, 'type']);
      }
    }
    if (typeof d.correlation === 'string') {
      if (!names.has(d.correlation)) report('error', 'event.correlation', ev, `Correlation field "${d.correlation}" is not a payload field of event "${ev.id}".`, ['correlation']);
      else if (role !== 'request' && !contractFields(contract, 'request').has(d.correlation)) report('error', 'event.correlation', ev, `Correlation field "${d.correlation}" is not an input of contract "${contract.id}", so no request can carry it.`, ['correlation']);
    }
  }

  // --- faults -------------------------------------------------------------
  for (const f of kind('fault')) {
    const k = f.data.kind;
    const need = (/** @type {string} */ prop) => { if (f.data[prop] === undefined) report('error', 'fault.missing', f, `A ${k} fault needs "${prop}".`); };
    if (['drop-event', 'delay-event', 'inject-event', 'duplicate-event', 'lose-event', 'retry-event'].includes(k)) need('event');
    if (k === 'delay-event') { need('by'); if (typeof f.data.by === 'number' && f.data.by <= 0) report('error', 'fault.value', f, '"by" must be positive.', ['by']); }
    if (k === 'duplicate-event' && typeof f.data.by === 'number' && f.data.by < 0) report('error', 'fault.value', f, '"by" must not be negative.', ['by']);
    if (k === 'retry-event') { need('attempts'); if (f.data.attempts !== undefined && !(Number.isInteger(f.data.attempts) && f.data.attempts >= 1)) report('error', 'fault.value', f, '"attempts" must be a positive integer.', ['attempts']); }
    if (k === 'inject-event') { need('at'); if (typeof f.data.at === 'number' && f.data.at < 0) report('error', 'fault.value', f, '"at" must not be negative.', ['at']); }
    if (k === 'enable-transition' || k === 'disable-transition') need('transition');
    if (k === 'enable-transition') {
      const t = get(f.data.transition);
      if (t && t.kind === 'transition' && t.data.faultOnly !== true) report('warning', 'fault.enable-not-faultonly', f, `Transition "${t.id}" is not marked faultOnly, so enabling it has no effect.`, ['transition']);
    }
    if (typeof f.data.occurrence === 'number' && (f.data.occurrence < 1 || !Number.isInteger(f.data.occurrence))) report('error', 'fault.value', f, '"occurrence" must be a positive integer.', ['occurrence']);
  }

  // --- scenarios ----------------------------------------------------------
  for (const s of kind('scenario')) {
    const bs = Array.isArray(s.data.behaviors) ? s.data.behaviors : [];
    if (!bs.length && !(Array.isArray(s.data.pools) && s.data.pools.length)) report('error', 'scenario.empty', s, 'A scenario needs at least one behavior or quota pool.', ['behaviors']);
    if (new Set(bs).size !== bs.length) report('error', 'scenario.duplicate-behavior', s, 'A behavior is listed twice.', ['behaviors']);
    (Array.isArray(s.data.steps) ? s.data.steps : []).forEach((/** @type {any} */ st, /** @type {number} */ i) => {
      if (st && typeof st.at === 'number' && st.at < 0) report('error', 'scenario.step-time', s, 'Step time "at" must not be negative.', ['steps', i]);
    });
    if (s.data.maxSteps !== undefined && !(Number.isInteger(s.data.maxSteps) && s.data.maxSteps > 0)) report('error', 'scenario.max-steps', s, '"maxSteps" must be a positive integer.', ['maxSteps']);
  }

  out.push(...scenarioInputDiagnostics(model));

  out.push(...validateFaultModels(model));

  // --- data model: consistency (errors) and the six data rules (warnings) --
  out.push(...checkDataConsistency(model));
  out.push(...dataRuleDiagnostics(model));

  // --- types, record constraints, requirement realisation, cross-cutting constructs, user interface, telemetry (errors); readiness when generation is declared --
  out.push(...checkCodegenConsistency(model));
  out.push(...checkTypeShapes(model));
  out.push(...checkLanguages(model));
  out.push(...checkFunctions(model));

  out.push(...checkTenantData(model));
  out.push(...checkDerivations(model));
  out.push(...checkSuppliedInputs(model));
  out.push(...checkConstructConsistency(model));
  out.push(...checkUiConsistency(model));
  out.push(...checkTelemetryConsistency(model));

  out.push(...checkAccessConsistency(model));
  out.push(...checkCapabilityConsistency(model));
  out.push(...checkResidency(model));
  out.push(...checkPools(model));
  if (model.system.data.generation !== undefined) {
    // The machine rules are reported above for every implementation-level behavior, switch or not.
    for (const g of READINESS_RULES.flatMap((rule) => rule(model))) {
      const e = get(g.entityId);
      out.push(e ? { ...g, loc: e.loc, path: e.path } : g);
    }
  }

  claimChecks();

  // --- integrity rules: invalid rules, vacuity and every current violation --
  out.push(...integrityDiagnostics(model));

  // --- views --------------------------------------------------------------
  for (const v of kind('view')) {
    const f = v.data.filter;
    if (f && typeof f === 'object') {
      for (const cat of Array.isArray(f.categories) ? f.categories : []) if (!own(model.meta.categories, cat)) report('error', 'view.filter', v, `Unknown category "${cat}" in view filter.`, ['filter', 'categories']);
      for (const rk of Array.isArray(f.relationshipKinds) ? f.relationshipKinds : []) if (!own(model.meta.relationshipKinds, rk)) report('error', 'view.filter', v, `Unknown relationship kind "${rk}" in view filter.`, ['filter', 'relationshipKinds']);
    }
  }

  // --- gaps (info) --------------------------------------------------------
  const touched = new Set();
  for (const r of kind('relationship')) for (const end of [r.data.from, r.data.to]) {
    const e = get(end);
    if (e) touched.add(e.kind === 'port' ? e.owner : e.id);
  }
  const hasChildren = new Set(kind('component').map((c) => c.data.parent).filter(Boolean));
  for (const e of model.entities.values()) {
    const def = model.meta.entities[e.kind];
    for (const [prop, pdef] of Object.entries(def.properties)) {
      if (!(/** @type {any} */ (pdef).expected)) continue;
      const v = e.data[prop];
      if (v === undefined || v === '' || (Array.isArray(v) && !v.length)) report('info', 'gap.missing-property', e, `${def.label} "${e.id}" does not state its ${/** @type {any} */ (pdef).label?.toLowerCase() ?? prop}.`);
    }
    if (e.kind === 'component') {
      if (e.data.kind === 'subsystem') { if (!hasChildren.has(e.id)) report('info', 'gap.empty-subsystem', e, `Subsystem "${e.id}" contains no components.`); }
      // A composite of another kind needs no relationship of its own: its members have them.
      else if (!touched.has(e.id) && !hasChildren.has(e.id)) report('info', 'gap.unconnected', e, `Component "${e.id}" takes part in no relationship.`);
      if (Array.isArray(e.data.unknowns) && e.data.unknowns.length) report('info', 'gap.unknowns', e, `Component "${e.id}" records ${e.data.unknowns.length} open unknown(s).`);
    }
  }
  const usedEvents = new Set();
  for (const r of model.refs) if (r.allowed.length === 1 && r.allowed[0] === 'event') usedEvents.add(r.target);
  // A logged domain event is emitted by the running system, which writes it to a service's log (telemetry.js).
  for (const ev of kind('event')) if (ev.data.domain === true && ev.data.logging?.logged === true) usedEvents.add(ev.id);
  for (const ev of kind('event')) if (!usedEvents.has(ev.id)) report('info', 'gap.unused-event', ev, `Event "${ev.id}" is never triggered, emitted or awaited.`);
  if (kind('faultModel').length) {
    for (const c of kind('claim')) {
      if (['invariant', 'temporal', 'measured'].includes(c.data.kind) && c.data.faultModel === undefined) report('info', 'gap.no-fault-model', c, `Claim "${c.id}" is evaluated under no fault model, though this specification declares ${kind('faultModel').length === 1 ? 'one' : 'some'}.`);
    }
  }
  // --- evidence -----------------------------------------------------------
  // A test reference that exegra verify would refuse as unsafe is an error here, so the author sees it before verify.
  for (const e of kind('evidence')) {
    if (e.data.kind !== 'test' || typeof e.data.ref !== 'string') continue;
    const problem = testRefProblem(e.data.ref);
    if (problem) report('error', 'evidence.ref-unsafe', e, `Evidence "${e.id}": ${describeTestRefProblem(e.data.ref, problem)}`, ['ref']);
  }
  const evidenced = new Set(kind('evidence').map((e) => e.data.claim));
  for (const c of kind('claim')) {
    if (c.data.kind !== 'requirement' && c.data.evaluate?.method === 'external-evidence' && !evidenced.has(c.id)) report('info', 'gap.no-evidence', c, `Claim "${c.id}" can only be supported by external evidence, and none is recorded.`);
  }

  return out;
}

/**
 * The well-formedness of the abstraction structure (docs/model-and-format.md, "Elements, hierarchies, facets
 * and cuts"): every hierarchy laminar and acyclic, every module element under exactly one element, facets
 * never used as contractions, and every cut an antichain that covers every element. The logical hierarchy's
 * cycles are component.parent-cycle, reported above.
 * @param {Model} model
 * @param {(severity: 'error'|'warning'|'info', code: string, entity: Entity, message: string, sub?: (string|number)[]) => void} report
 */
function checkAbstraction(model, report) {
  const get = (/** @type {string} */ id) => model.entities.get(id);
  const facetAt = (/** @type {any} */ id) => typeof id === 'string' && get(id)?.kind === 'facet';
  // Module elements: one owner each.
  const logical = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, LOGICAL));
  const decls = moduleDeclarations(model);
  for (const p of logical.problems) {
    if (p.code !== 'multiple-owners') continue;
    const owners = p.others ?? [];
    for (const d of decls) {
      if (d.id !== p.element || d.component === owners[0]) continue;
      const c = get(d.component);
      if (c) report('error', 'module.multiple-owners', c, p.message, ['implementation', 'modules', d.index]);
    }
  }
  // Declared hierarchies.
  for (const h of model.byKind.hierarchy ?? []) {
    if (h.id === LOGICAL) report('error', 'hierarchy.reserved-id', h, `"${LOGICAL}" is the hierarchy component.parent declares; a declared hierarchy needs another id.`, ['id']);
    (Array.isArray(h.data.groups) ? h.data.groups : []).forEach((/** @type {any} */ g, /** @type {number} */ i) => {
      if (g && facetAt(g.parent)) report('error', 'facet.contraction', h, `Hierarchy "${h.id}" places members under facet "${g.parent}"; a facet may overlap other groupings, so it is never a parent in a hierarchy.`, ['groups', i, 'parent']);
    });
    const by = h.data.groupBy;
    if (by && by.parents && typeof by.parents === 'object') {
      for (const [v, p] of Object.entries(by.parents)) {
        if (facetAt(p)) report('error', 'facet.contraction', h, `Hierarchy "${h.id}" places the elements whose "${by.property}" is "${v}" under facet "${p}"; a facet is never a parent in a hierarchy.`, ['groupBy', 'parents', v]);
        else if (typeof p !== 'string') report('error', 'hierarchy.unknown-parent', h, `groupBy.parents."${v}" must be an element id.`, ['groupBy', 'parents', v]);
      }
    }
    const built = hierarchyOf(model, h.id);
    for (const p of built?.problems ?? []) {
      if (p.code === 'multiple-parents') report('error', 'hierarchy.multiple-parents', h, p.message, p.at?.path);
      else if (p.code === 'cycle') report('error', 'hierarchy.cycle', h, p.message, ['groups']);
      else if (p.code === 'unknown-parent' && !facetAt(p.others?.[0])) report('error', 'hierarchy.unknown-parent', h, p.message, p.at?.path);
    }
  }
  // Cuts.
  /** @type {Record<string, string>} */
  const CUT_CODES = { 'not-composite': 'cut.not-composite', 'ancestor-not-expanded': 'cut.ancestor-not-expanded', uncovered: 'cut.uncovered', 'not-antichain': 'cut.not-antichain' };
  for (const c of model.byKind.cut ?? []) {
    const d = c.data;
    const hid = cutHierarchyId(c);
    if (facetAt(hid)) { report('error', 'facet.contraction', c, `Cut "${c.id}" is a cut of facet "${hid}"; a facet may overlap, so it has no cuts. Name a hierarchy.`, ['hierarchy']); continue; }
    for (const key of ['expand', 'blocks']) {
      (Array.isArray(d[key]) ? d[key] : []).forEach((/** @type {any} */ x, /** @type {number} */ i) => {
        if (facetAt(x)) report('error', 'facet.contraction', c, `Cut "${c.id}" ${key === 'expand' ? 'expands' : 'has as a block'} facet "${x}"; a facet is never contracted or expanded, only selected.`, [key, i]);
      });
    }
    if (Array.isArray(d.blocks) && (d.expand !== undefined || d.depth !== undefined || d.finest !== undefined)) {
      report('error', 'cut.form', c, `Cut "${c.id}" lists its blocks and also expand, depth or finest; give the blocks, or the expansion, not both.`, ['blocks']);
    }
    if (d.depth !== undefined && !(Number.isInteger(d.depth) && d.depth >= 0)) report('error', 'cut.form', c, `The depth of cut "${c.id}" must be a whole number of at least 0.`, ['depth']);
    const m = cutMap(model, c.id);
    if (!m) continue;
    for (const p of m.problems) {
      const code = CUT_CODES[p.code];
      if (!code) continue;
      const key = Array.isArray(d.blocks) ? 'blocks' : 'expand';
      const list = Array.isArray(d[key]) ? d[key] : [];
      const i = list.indexOf(p.element);
      report('error', code, c, `Cut "${c.id}": ${p.message}`, i >= 0 ? [key, i] : undefined);
    }
  }
}
