// Semantic validation: rules that need the whole model rather than one value.
// Structural/type checks happen in parse.js. Severity meaning:
//   error   - the model is not well-formed; transactions producing errors are rejected
//   warning - well-formed but suspicious or unsupported (e.g. unknown claim method)
//   info    - a gap: something a complete specification is expected to state

import { parseExpr, exprRefs } from './expr.js';
import { CLAIM_METHODS } from './claim-methods.js';
import { own } from './own.js';
import { validateFaultModels } from './fault-model.js';
import { checkDataConsistency, dataRuleDiagnostics, RULE_IDS } from './data-model.js';
import { contractFields, contractErrorCodes } from './contract-trace.js';
import { parseType, typeAssignable, typeText } from './type-expr.js';
import { integrityDiagnostics } from './integrity.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

const VAR_RE = /^[A-Za-z_][A-Za-z0-9_]*$/;
const RESERVED_VARS = ['state', 'event', 'time', 'true', 'false', 'null'];

/**
 * @param {Model} model
 * @returns {Diagnostic[]}
 */
export function validateModel(model) {
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
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];

  // --- components ---------------------------------------------------------
  for (const c of kind('component')) {
    const parentId = c.data.parent;
    if (typeof parentId === 'string') {
      const parent = get(parentId);
      if (parent && parent.kind === 'component' && parent.data.kind !== 'subsystem') {
        report('error', 'component.parent-not-subsystem', c, `Parent "${parentId}" is not declared with kind "subsystem".`, ['parent']);
      }
      const seen = new Set([c.id]);
      let cur = parent;
      while (cur && cur.kind === 'component') {
        if (seen.has(cur.id)) { report('error', 'component.parent-cycle', c, `Containment cycle through "${cur.id}".`, ['parent']); break; }
        seen.add(cur.id);
        cur = typeof cur.data.parent === 'string' ? get(cur.data.parent) : undefined;
      }
    }
  }

  // --- relationships ------------------------------------------------------
  const relKeys = new Map();
  for (const r of kind('relationship')) {
    if (r.data.from === r.data.to) report('warning', 'relationship.self', r, 'Relationship connects an entity to itself.');
    const key = `${r.data.kind}|${r.data.from}|${r.data.to}`;
    if (relKeys.has(key)) report('warning', 'relationship.duplicate', r, `Same kind and endpoints as relationship "${relKeys.get(key)}".`);
    else relKeys.set(key, r.id);
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

  for (const b of kind('behavior')) {
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
    const reach = new Set([b.data.initial]);
    let grew = true;
    while (grew) {
      grew = false;
      for (const t of transitions) if (reach.has(t.data.from) && !reach.has(t.data.to)) { reach.add(t.data.to); grew = true; }
    }
    for (const s of states) if (!reach.has(s.id)) report('warning', 'behavior.unreachable-state', s, `State "${s.id}" cannot be reached from the initial state of "${b.id}".`);
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
        else if (typeof fx.to !== v.type) report('error', 'effect.value', t, `Effect sets ${v.type} variable "${fx.set}" to ${JSON.stringify(fx.to)}.`, sub);
      } else if ('emit' in fx) {
        for (const k of keys) if (!['emit', 'after', 'payload'].includes(k)) report('error', 'effect.unknown', t, `Unsupported field "${k}" in an "emit" effect.`, sub);
        if (typeof fx.emit !== 'string') report('error', 'effect.emit', t, 'Effect "emit" must be an event id.', sub);
        if ('after' in fx && !(typeof fx.after === 'number' && fx.after >= 0)) report('error', 'effect.after', t, 'Effect "after" must be a non-negative number of logical ticks.', sub);
        if ('payload' in fx) {
          if (!fx.payload || typeof fx.payload !== 'object' || Array.isArray(fx.payload)) report('error', 'effect.payload', t, 'Effect "payload" must be an object.', sub);
          else for (const [k, v] of Object.entries(fx.payload)) if (typeof v === 'string') checkExpr(v, t, [...sub, 'payload', k], scope);
        }
      } else {
        report('error', 'effect.unknown', t, 'An effect must be {"set": variable, "to": value} or {"emit": event}.', sub);
      }
    });
  }

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
    if (k === 'drop-event' || k === 'delay-event' || k === 'inject-event') need('event');
    if (k === 'delay-event') { need('by'); if (typeof f.data.by === 'number' && f.data.by <= 0) report('error', 'fault.value', f, '"by" must be positive.', ['by']); }
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
    if (!bs.length) report('error', 'scenario.empty', s, 'A scenario needs at least one behavior.', ['behaviors']);
    if (new Set(bs).size !== bs.length) report('error', 'scenario.duplicate-behavior', s, 'A behavior is listed twice.', ['behaviors']);
    (Array.isArray(s.data.steps) ? s.data.steps : []).forEach((/** @type {any} */ st, /** @type {number} */ i) => {
      if (st && typeof st.at === 'number' && st.at < 0) report('error', 'scenario.step-time', s, 'Step time "at" must not be negative.', ['steps', i]);
    });
    if (s.data.maxSteps !== undefined && !(Number.isInteger(s.data.maxSteps) && s.data.maxSteps > 0)) report('error', 'scenario.max-steps', s, '"maxSteps" must be a positive integer.', ['maxSteps']);
  }

  out.push(...validateFaultModels(model));

  // --- data model: consistency (errors) and the five data rules (warnings) --
  out.push(...checkDataConsistency(model));
  out.push(...dataRuleDiagnostics(model));

  // --- claims -------------------------------------------------------------
  for (const c of kind('claim')) {
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
    /** @type {Set<string>|undefined} */
    let allowedBehaviors;
    if (Array.isArray(ev.scenarios)) {
      for (const sid of ev.scenarios) {
        const sc = get(sid);
        if (!sc || sc.kind !== 'scenario') continue;
        const set = new Set(Array.isArray(sc.data.behaviors) ? sc.data.behaviors : []);
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
          for (const k of Object.keys(v)) if (!['ids', 'category', 'kind', 'tag', 'trustZone', 'within', 'all'].includes(k)) report('error', 'claim.selector.unknown', c, `Unsupported selector field "${k}".`, [...sub, k]);
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
    if (ev.method === 'eventually' && ev.occurs === undefined && ev.expr === undefined) report('error', 'claim.param.required', c, 'Method "eventually" needs "occurs" or "expr".', ['evaluate']);
  }

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
      else if (!touched.has(e.id)) report('info', 'gap.unconnected', e, `Component "${e.id}" takes part in no relationship.`);
      if (Array.isArray(e.data.unknowns) && e.data.unknowns.length) report('info', 'gap.unknowns', e, `Component "${e.id}" records ${e.data.unknowns.length} open unknown(s).`);
    }
  }
  const usedEvents = new Set();
  for (const r of model.refs) if (r.allowed.length === 1 && r.allowed[0] === 'event') usedEvents.add(r.target);
  for (const ev of kind('event')) if (!usedEvents.has(ev.id)) report('info', 'gap.unused-event', ev, `Event "${ev.id}" is never triggered, emitted or awaited.`);
  if (kind('faultModel').length) {
    for (const c of kind('claim')) {
      if (['invariant', 'temporal', 'measured'].includes(c.data.kind) && c.data.faultModel === undefined) report('info', 'gap.no-fault-model', c, `Claim "${c.id}" is evaluated under no fault model, though this specification declares ${kind('faultModel').length === 1 ? 'one' : 'some'}.`);
    }
  }
  const evidenced = new Set(kind('evidence').map((e) => e.data.claim));
  for (const c of kind('claim')) {
    if (c.data.kind !== 'requirement' && c.data.evaluate?.method === 'external-evidence' && !evidenced.has(c.id)) report('info', 'gap.no-evidence', c, `Claim "${c.id}" can only be supported by external evidence, and none is recorded.`);
  }

  return out;
}
