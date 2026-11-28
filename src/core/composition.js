// Behavioural composition along the hierarchy (WG-5729; docs/composition.md): event interfaces of elements
// and ports, composite behaviour with internal events hidden, declared abstractions of member sets and
// their refinement check, behavioural cuts and environment assumptions of scenarios, order independence of
// composition, claim transfer by preservation rules, and same-subject alternative machines.
//
// Nothing here runs behaviour of its own. A composition is a set of machines run together in one engine
// input (the kernel elaborates it into one calculus system); hiding and the comparison of two runs are
// computed in Lean (formal/Exegra/Boundary.lean, `engine.boundary` and `engine.refineBoundary` at the call
// boundary), on traces the Lean engine produced. This module derives the inputs, the alphabets and the
// hidden sets from the model, and formats the results.

import { engineInput, runEngine } from './engine.js';
import { call } from './lean.js';
import { parseExpr, exprRefs } from './expr.js';
import { ancestorsOf, descendantsOf, childrenOf } from './query.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/**
 * @typedef {{inputs: string[], outputs: string[], observables: string[]}} Interface
 * @typedef {{inputs: string[], outputs: string[], internal: string[], observables: string[], behaviors: string[]}} InferredInterface
 * @typedef {{reader: string, readerElement: string, target: string, targetElement: string, observable: string,
 *   transition: string, crosses: string[], exportedBy: string[], unexportedBy: string[]}} CrossRead
 *   crosses: the elements with a declared interface whose boundary the read crosses; exportedBy / unexportedBy split
 *   them by whether their interface exports the observable
 * @typedef {{behavior: string, members: string[], hide: string[]|null, timeScale: number}} Abstraction
 */

const obj = (/** @type {any} */ v) => (v && typeof v === 'object' && !Array.isArray(v) ? v : null);
const strs = (/** @type {any} */ v) => (Array.isArray(v) ? v.filter((x) => typeof x === 'string') : []);
const uniq = (/** @type {string[]} */ xs) => [...new Set(xs)];
const sorted = (/** @type {Iterable<string>} */ xs) => [...new Set(xs)].sort();

// ---------------------------------------------------------------------------
// Alphabets of behaviours
// ---------------------------------------------------------------------------

/**
 * The events a behaviour consumes (transition triggers) and emits (emit and timer effects), and the
 * references its guards and effects make to other behaviours' state (`<behavior>.<variable>`, `<behavior>.state`).
 * @param {Model} model @param {string} bid
 * @returns {{inputs: Set<string>, outputs: Set<string>, reads: {target: string, name: string, transition: string}[]}}
 */
export function alphabetOf(model, bid) {
  const inputs = new Set(), outputs = new Set();
  /** @type {{target: string, name: string, transition: string}[]} */
  const reads = [];
  const behaviorIds = new Set((model.byKind.behavior ?? []).map((b) => b.id));
  /** @param {any} src @param {string} tid */
  const scan = (src, tid) => {
    if (typeof src !== 'string') return;
    const p = parseExpr(src);
    if (!p.ok) return;
    for (const path of exprRefs(p.ast)) {
      if (path.length === 2 && path[0] !== 'event' && path[0] !== bid && behaviorIds.has(path[0])) reads.push({ target: path[0], name: path[1], transition: tid });
    }
  };
  for (const t of model.byKind.transition ?? []) {
    if (t.owner !== bid) continue;
    if (typeof t.data.on === 'string') inputs.add(t.data.on);
    scan(t.data.guard, t.id);
    for (const fx of Array.isArray(t.data.effects) ? t.data.effects : []) {
      if (!fx || typeof fx !== 'object') continue;
      if (typeof fx.emit === 'string') outputs.add(fx.emit);
      scan(fx.to, t.id);
      for (const v of Object.values(obj(fx.payload) ?? {})) scan(v, t.id);
    }
  }
  return { inputs, outputs, reads };
}

/** All events a behaviour consumes or emits. @param {Model} model @param {string} bid */
function eventsOf(model, bid) {
  const a = alphabetOf(model, bid);
  return new Set([...a.inputs, ...a.outputs]);
}

// ---------------------------------------------------------------------------
// Elements, members and interfaces
// ---------------------------------------------------------------------------

/** The element itself and its ancestors in the logical (parent) hierarchy. @param {Model} model @param {string} id */
function selfAndAncestors(model, id) {
  return [id, ...ancestorsOf(model, id)];
}

/** Whether element `id` is `root` or lies inside it. @param {Model} model @param {string} id @param {string} root */
export function within(model, id, root) {
  return selfAndAncestors(model, id).includes(root);
}

/**
 * A behaviour's declared abstraction of a member set, or null (docs/composition.md, "Declared abstractions").
 * @param {Model} model @param {string|Entity} b
 * @returns {Abstraction|null}
 */
export function abstractionOf(model, b) {
  const e = typeof b === 'string' ? model.entities.get(b) : b;
  if (!e || e.kind !== 'behavior') return null;
  const a = obj(e.data.abstracts);
  if (!a) return null;
  const ts = typeof a.timeScale === 'number' && Number.isFinite(a.timeScale) && a.timeScale > 0 ? a.timeScale : 1;
  return { behavior: e.id, members: strs(a.members), hide: Array.isArray(a.hide) ? strs(a.hide) : null, timeScale: ts };
}

/** The behaviours that are not declared abstractions: the finest machines of their subjects. @param {Model} model */
function leafBehaviors(model) {
  return (model.byKind.behavior ?? []).filter((b) => !abstractionOf(model, b));
}

/**
 * The machines that run in place of an abstraction at its members' level: its members, and with `finest`, the
 * members of members that are abstractions themselves, recursively.
 * @param {Model} model @param {string} aid @param {{finest?: boolean}} [opts]
 * @returns {string[]}
 */
export function membersOf(model, aid, opts = {}) {
  const out = [];
  const seen = new Set([aid]);
  /** @param {string} id */
  const walk = (id) => {
    const a = abstractionOf(model, id);
    for (const m of a?.members ?? []) {
      if (seen.has(m)) continue;
      seen.add(m);
      if (opts.finest && abstractionOf(model, m)) walk(m);
      else out.push(m);
    }
  };
  walk(aid);
  return out;
}

/** The elements a declared abstraction stands for: the subjects of its finest members. @param {Model} model @param {string} aid */
export function regionOf(model, aid) {
  return sorted(membersOf(model, aid, { finest: true }).map((m) => model.entities.get(m)?.data.subject).filter((s) => typeof s === 'string'));
}

/**
 * The declared interface of a component or port, or null.
 * @param {Model} model @param {string} id
 * @returns {Interface|null}
 */
export function declaredInterface(model, id) {
  const e = model.entities.get(id);
  const i = obj(e?.data.interface);
  if (!e || !i) return null;
  return { inputs: strs(i.inputs), outputs: strs(i.outputs), observables: strs(i.observables) };
}

/**
 * The interface of an element read off its members' behaviours: the behaviours whose subject is the element or
 * lies inside it (declared abstractions excluded, so a member set is not counted twice). An input is an event a
 * member consumes that some behaviour outside emits or that no behaviour emits (it comes from outside the
 * model); an output is an event a member emits that some behaviour outside consumes or that no behaviour
 * consumes; the internal events are the members' other events. The observables are the members' variables and
 * control states that behaviours outside read.
 * @param {Model} model @param {string} elementId
 * @returns {InferredInterface}
 */
export function inferredInterface(model, elementId) {
  const all = leafBehaviors(model);
  const members = all.filter((b) => typeof b.data.subject === 'string' && within(model, b.data.subject, elementId));
  const outside = all.filter((b) => !members.includes(b));
  const alphaMap = new Map(all.map((b) => [b.id, alphabetOf(model, b.id)]));
  const alpha = { get: (/** @type {string} */ id) => /** @type {ReturnType<typeof alphabetOf>} */ (alphaMap.get(id)) };
  const inEvents = new Set(members.flatMap((b) => [...alpha.get(b.id).inputs]));
  const outEvents = new Set(members.flatMap((b) => [...alpha.get(b.id).outputs]));
  const emittedOutside = new Set(outside.flatMap((b) => [...alpha.get(b.id).outputs]));
  const consumedOutside = new Set(outside.flatMap((b) => [...alpha.get(b.id).inputs]));
  const emittedAnywhere = new Set(all.flatMap((b) => [...alpha.get(b.id).outputs]));
  const consumedAnywhere = new Set(all.flatMap((b) => [...alpha.get(b.id).inputs]));
  const inputs = [...inEvents].filter((e) => emittedOutside.has(e) || !emittedAnywhere.has(e));
  const outputs = [...outEvents].filter((e) => consumedOutside.has(e) || !consumedAnywhere.has(e));
  const boundary = new Set([...inputs, ...outputs]);
  const internal = [...new Set([...inEvents, ...outEvents])].filter((e) => !boundary.has(e));
  const memberIds = new Set(members.map((b) => b.id));
  const observables = outside.flatMap((b) => alpha.get(b.id).reads.filter((r) => memberIds.has(r.target)).map((r) => `${r.target}.${r.name}`));
  return { inputs: sorted(inputs), outputs: sorted(outputs), internal: sorted(internal), observables: sorted(observables), behaviors: members.map((b) => b.id) };
}

/**
 * Every cross-element state read: a guard or effect of one behaviour that reads the state of a behaviour whose
 * subject is another element. Each such read is an interaction on the target's boundary; where the read crosses
 * the boundary of an element with a declared interface, that interface must export the observable.
 * @param {Model} model
 * @returns {CrossRead[]}
 */
export function crossReads(model) {
  /** @type {CrossRead[]} */
  const out = [];
  const declared = (model.byKind.component ?? []).filter((c) => declaredInterface(model, c.id));
  for (const b of model.byKind.behavior ?? []) {
    const r = typeof b.data.subject === 'string' ? b.data.subject : null;
    if (!r) continue;
    for (const read of alphabetOf(model, b.id).reads) {
      const tb = model.entities.get(read.target);
      const t = typeof tb?.data.subject === 'string' ? tb.data.subject : null;
      if (!t || t === r) continue;
      const observable = `${read.target}.${read.name}`;
      const crosses = declared.filter((c) => within(model, t, c.id) && !within(model, r, c.id)).map((c) => c.id);
      const exportedBy = crosses.filter((c) => declaredInterface(model, c)?.observables.includes(observable));
      out.push({ reader: b.id, readerElement: r, target: read.target, targetElement: t, observable, transition: read.transition, crosses, exportedBy, unexportedBy: crosses.filter((c) => !exportedBy.includes(c)) });
    }
  }
  return out;
}

/**
 * The interfaces an event belongs to: declared ones (an element's or port's inputs or outputs), inferred ones
 * (the subject of a behaviour that consumes or emits it) and the element `producedBy` names.
 * @param {Model} model
 * @returns {Map<string, {element: string, via: 'declared'|'inferred'|'producedBy', direction: 'input'|'output'|'internal'}[]>}
 */
export function eventInterfaces(model) {
  /** @type {Map<string, {element: string, via: 'declared'|'inferred'|'producedBy', direction: 'input'|'output'|'internal'}[]>} */
  const out = new Map((model.byKind.event ?? []).map((e) => [e.id, []]));
  const add = (/** @type {string} */ ev, /** @type {any} */ x) => { if (out.has(ev)) out.get(ev)?.push(x); };
  for (const k of ['component', 'port']) {
    for (const e of model.byKind[k] ?? []) {
      const i = declaredInterface(model, e.id);
      if (!i) continue;
      for (const ev of i.inputs) add(ev, { element: e.id, via: 'declared', direction: 'input' });
      for (const ev of i.outputs) add(ev, { element: e.id, via: 'declared', direction: 'output' });
    }
  }
  for (const b of model.byKind.behavior ?? []) {
    if (typeof b.data.subject !== 'string') continue;
    const a = alphabetOf(model, b.id);
    for (const ev of a.inputs) add(ev, { element: b.data.subject, via: 'inferred', direction: 'input' });
    for (const ev of a.outputs) add(ev, { element: b.data.subject, via: 'inferred', direction: 'output' });
  }
  for (const e of model.byKind.event ?? []) {
    const p = e.data.producedBy;
    for (const el of typeof p === 'string' ? [p] : strs(p)) add(e.id, { element: el, via: 'producedBy', direction: 'output' });
  }
  return out;
}

/**
 * The interface report of an element (or of every element that has behaviours or a declared interface).
 * @param {Model} model @param {string} [elementId]
 */
export function interfaceReport(model, elementId) {
  const ids = elementId ? [elementId] : sorted([
    ...(model.byKind.behavior ?? []).map((b) => b.data.subject).filter((s) => typeof s === 'string'),
    ...(model.byKind.component ?? []).filter((c) => declaredInterface(model, c.id)).map((c) => c.id),
  ]);
  const reads = crossReads(model);
  return ids.map((id) => {
    const declared = declaredInterface(model, id);
    const inferred = inferredInterface(model, id);
    const missing = declared ? {
      inputs: inferred.inputs.filter((e) => !declared.inputs.includes(e)),
      outputs: inferred.outputs.filter((e) => !declared.outputs.includes(e)),
    } : null;
    return {
      element: id,
      declared,
      inferred,
      status: declared ? (missing && (missing.inputs.length || missing.outputs.length) ? 'disagrees' : 'declared') : 'inferred',
      ...(missing ? { missing } : {}),
      reads: reads.filter((r) => within(model, r.targetElement, id) && !within(model, r.readerElement, id)),
    };
  });
}

// ---------------------------------------------------------------------------
// Same-subject alternative machines
// ---------------------------------------------------------------------------

/**
 * Pairs of behaviours of one subject that consume a common event, are listed together in no scenario, and are
 * not related by a declared abstraction (one a member, at any depth, of the other) or by `refines`. Such machines
 * are alternative models of one element at one level: they never run together, so nothing shows that they agree
 * (docs/composition.md, "One behaviour per element per level").
 * @param {Model} model
 * @returns {{subject: string, a: string, b: string, shared: string[]}[]}
 */
export function alternativeMachines(model) {
  const bs = model.byKind.behavior ?? [];
  const scenarios = (model.byKind.scenario ?? []).map((s) => new Set(strs(s.data.behaviors)));
  /** Every member at any depth, abstractions in between included. @param {string} x */
  const below = (x) => [...membersOf(model, x, { finest: true }), ...collectAbstractions(model, x)];
  const related = (/** @type {string} */ x, /** @type {string} */ y) =>
    below(x).includes(y) || below(y).includes(x)
    || model.entities.get(x)?.data.refines === y || model.entities.get(y)?.data.refines === x;
  const out = [];
  for (let i = 0; i < bs.length; i++) {
    for (let j = i + 1; j < bs.length; j++) {
      const a = bs[i], b = bs[j];
      if (a.data.subject !== b.data.subject || typeof a.data.subject !== 'string') continue;
      if (abstractionOf(model, a) || abstractionOf(model, b)) {
        if (related(a.id, b.id)) continue;
      } else if (related(a.id, b.id)) continue;
      const ia = alphabetOf(model, a.id).inputs, ib = alphabetOf(model, b.id).inputs;
      const shared = [...ia].filter((e) => ib.has(e));
      if (!shared.length) continue;
      if (scenarios.some((s) => s.has(a.id) && s.has(b.id))) continue;
      out.push({ subject: a.data.subject, a: a.id, b: b.id, shared: sorted(shared) });
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Behavioural cuts of scenarios
// ---------------------------------------------------------------------------

/**
 * A scenario's behavioural cut: for each region (a declared abstraction), the level that runs, declared or
 * inferred from the behaviours it lists; and its environment assumptions. A view may display it; nothing a view
 * holds changes it.
 * @param {Model} model @param {string} sid
 */
export function scenarioCut(model, sid) {
  const s = model.entities.get(sid);
  if (!s || s.kind !== 'scenario') throw new Error(`"${sid}" is not a scenario in this model.`);
  const cut = obj(s.data.cut) ?? {};
  const listed = strs(s.data.behaviors);
  const declared = (Array.isArray(cut.regions) ? cut.regions : []).filter((/** @type {any} */ r) => obj(r) && typeof r.abstraction === 'string');
  /** @type {{abstraction: string, level: 'abstract'|'members', declared: boolean, region: string[]}[]} */
  const regions = declared.map((/** @type {any} */ r) => ({ abstraction: r.abstraction, level: r.level === 'members' ? 'members' : 'abstract', declared: true, region: regionOf(model, r.abstraction) }));
  for (const b of model.byKind.behavior ?? []) {
    if (!abstractionOf(model, b) || regions.some((r) => r.abstraction === b.id)) continue;
    const members = membersOf(model, b.id);
    if (listed.includes(b.id)) regions.push({ abstraction: b.id, level: 'abstract', declared: false, region: regionOf(model, b.id) });
    else if (members.length && members.every((m) => listed.includes(m))) regions.push({ abstraction: b.id, level: 'members', declared: false, region: regionOf(model, b.id) });
  }
  const environment = (Array.isArray(cut.environment) ? cut.environment : []).filter(obj).map((/** @type {any} */ e) => ({
    element: typeof e.element === 'string' ? e.element : null,
    assumption: typeof e.assumption === 'string' ? e.assumption : null,
    events: strs(e.events),
    note: typeof e.note === 'string' ? e.note : null,
  }));
  return { scenario: sid, behaviors: listed, regions, environment };
}

/**
 * The behaviours of a scenario with some regions run at another level: each `levels` entry maps an abstraction
 * to 'abstract' (its members, at any depth, are replaced by it) or 'members' (it is replaced by its members).
 * Faults that act on a transition of a machine that no longer runs are left out and listed.
 * @param {Model} model @param {string} sid @param {Record<string, 'abstract'|'members'|'finest'>} levels @param {string[]} [faults]
 * @returns {{behaviors: string[], faults: string[], droppedFaults: string[], replaced: {abstraction: string, level: string, removed: string[], added: string[]}[]}}
 */
export function behaviorsAtLevels(model, sid, levels, faults) {
  const s = model.entities.get(sid);
  if (!s || s.kind !== 'scenario') throw new Error(`"${sid}" is not a scenario in this model.`);
  let list = strs(s.data.behaviors);
  const replaced = [];
  for (const [aid, level] of Object.entries(levels)) {
    if (!abstractionOf(model, aid)) throw new Error(`"${aid}" is not a behavior that declares an abstraction ("abstracts").`);
    const deep = membersOf(model, aid, { finest: true });
    const all = uniq([...membersOf(model, aid), ...deep, ...collectAbstractions(model, aid)]);
    if (level === 'abstract') {
      const at = list.findIndex((b) => all.includes(b));
      if (list.includes(aid)) { replaced.push({ abstraction: aid, level, removed: [], added: [] }); continue; }
      if (at < 0) throw new Error(`Scenario "${sid}" runs neither "${aid}" nor any of its members.`);
      const removed = list.filter((b) => all.includes(b));
      list = [...list.slice(0, at).filter((b) => !all.includes(b)), aid, ...list.slice(at).filter((b) => !all.includes(b))];
      replaced.push({ abstraction: aid, level, removed, added: [aid] });
    } else {
      const members = level === 'finest' ? deep : membersOf(model, aid);
      const at = list.indexOf(aid);
      if (at < 0) {
        // The scenario runs the members already: all of them, or the ones it needs (a scenario that leaves out a member
        // the abstraction also stands for runs the region at the members it lists; an element no running machine covers
        // makes the refinement check incomplete, never certified).
        if (members.some((m) => list.includes(m))) { replaced.push({ abstraction: aid, level, removed: [], added: [] }); continue; }
        throw new Error(`Scenario "${sid}" does not run "${aid}".`);
      }
      const added = members.filter((m) => !list.includes(m));
      list = [...list.slice(0, at), ...added, ...list.slice(at + 1)];
      replaced.push({ abstraction: aid, level, removed: [aid], added });
    }
  }
  const running = new Set(list);
  const wanted = uniq(faults ?? strs(s.data.faults));
  const droppedFaults = wanted.filter((f) => {
    const fe = model.entities.get(f);
    if (fe?.kind !== 'fault' || typeof fe.data.transition !== 'string') return false;
    const t = model.entities.get(fe.data.transition);
    return !t || !running.has(/** @type {string} */ (t.owner));
  });
  return { behaviors: list, faults: wanted.filter((f) => !droppedFaults.includes(f)), droppedFaults, replaced };
}

/** The abstractions nested below an abstraction (members that declare abstractions, at any depth). @param {Model} model @param {string} aid */
function collectAbstractions(model, aid) {
  /** @type {string[]} */
  const out = [];
  const seen = new Set([aid]);
  /** @param {string} id */
  const walk = (id) => {
    for (const m of abstractionOf(model, id)?.members ?? []) {
      if (seen.has(m) || !abstractionOf(model, m)) continue;
      seen.add(m);
      out.push(m);
      walk(m);
    }
  };
  walk(aid);
  return out;
}

/**
 * The engine input of a scenario run with another list of behaviours (and faults): the scenario as written,
 * with only its `behaviors` (and fault list) replaced. The model is not changed.
 * @param {Model} model @param {string} sid @param {string[]} behaviors @param {string[]} [faults]
 */
export function inputWith(model, sid, behaviors, faults) {
  const s = /** @type {Entity} */ (model.entities.get(sid));
  const entities = new Map(model.entities);
  entities.set(sid, { ...s, data: { ...s.data, behaviors, ...(faults ? { faults } : {}) } });
  const shadow = /** @type {Model} */ (Object.assign(Object.create(Object.getPrototypeOf(model)), model, { entities }));
  return engineInput(shadow, sid, faults);
}

/**
 * The events a run delivered that no machine of the run reacts to (no transition of a running behaviour is
 * triggered by them) and that an element the scenario omits would receive: an element with a behaviour that
 * consumes the event, or whose declared interface (or one of its ports') lists it as an input. Each such delivery
 * needs an environment assumption of the scenario naming the element and the event; the others are reported.
 * @param {Model} model @param {string} sid @param {any} trace @param {string[]} [behaviors] the behaviours of the run (default: the scenario's)
 */
export function environmentReport(model, sid, trace, behaviors) {
  const cut = scenarioCut(model, sid);
  const running = new Set(behaviors ?? cut.behaviors);
  const runningSubjects = new Set([...running].map((b) => model.entities.get(b)?.data.subject).filter(Boolean));
  const consumedInRun = new Set([...running].flatMap((b) => [...alphabetOf(model, b).inputs]));
  /** @type {Map<string, Set<string>>} */
  const receivers = new Map();
  for (const b of model.byKind.behavior ?? []) {
    if (running.has(b.id) || typeof b.data.subject !== 'string') continue;
    for (const e of alphabetOf(model, b.id).inputs) { if (!receivers.has(e)) receivers.set(e, new Set()); receivers.get(e)?.add(b.data.subject); }
  }
  for (const k of ['component', 'port']) {
    for (const el of model.byKind[k] ?? []) {
      const i = declaredInterface(model, el.id);
      const owner = k === 'port' ? /** @type {string} */ (el.owner) : el.id;
      for (const e of i?.inputs ?? []) { if (!receivers.has(e)) receivers.set(e, new Set()); receivers.get(e)?.add(owner); }
    }
  }
  const covered = (/** @type {string} */ el, /** @type {string} */ ev) => cut.environment.some((x) => x.element === el && x.events.includes(ev));
  /** @type {{step: number, event: string, emitter: string|null, receivers: string[]}[]} */
  const assumed = [], unassumed = [];
  for (const st of trace.steps ?? []) {
    if (st.kind !== 'deliver' || st.error) continue;
    const ev = st.event?.id;
    if (!ev || consumedInRun.has(ev)) continue;
    // Receivers that are themselves running (an element whose other behaviour runs) do not stand for an omitted element.
    const rs = [...(receivers.get(ev) ?? [])].filter((r) => !runningSubjects.has(r));
    if (!rs.length) continue;
    const src = st.event?.source;
    const emitter = src?.kind === 'transition' ? src.behavior : src?.kind === 'scenario' ? 'scenario' : src?.kind === 'fault' ? `fault ${src.fault}` : null;
    const missing = rs.filter((r) => !covered(r, ev));
    (missing.length ? unassumed : assumed).push({ step: st.index, event: ev, emitter, receivers: missing.length ? missing : rs });
  }
  return { scenario: sid, environment: cut.environment, assumed, unassumed };
}

// ---------------------------------------------------------------------------
// Composite behaviour and the boundary refinement check
// ---------------------------------------------------------------------------

/**
 * The events hidden when a run of `members` (inside the region) is compared with a run of the abstraction:
 * the members' events that the abstraction does not know and that no machine outside the region (`others`) and
 * no scenario input or injected fault uses. A declared `hide` list replaces the derived one.
 * @param {Model} model @param {string} aid @param {string[]} members @param {string[]} others @param {string[]} inputs
 */
export function hiddenFor(model, aid, members, others, inputs) {
  const a = abstractionOf(model, aid);
  if (a?.hide) return sorted(a.hide);
  const own = eventsOf(model, aid);
  const outside = new Set([...others.flatMap((b) => [...eventsOf(model, b)]), ...inputs]);
  return sorted(members.flatMap((m) => [...eventsOf(model, m)]).filter((e) => !own.has(e) && !outside.has(e)));
}

/**
 * The derived behaviour of an element in a scenario: the scenario's machines whose subject lies in the element,
 * run with the rest (the kernel composes them), with the events internal to the element hidden. Exact: the
 * boundary trace is a projection of the composed run, computed in Lean (`engine.boundary`).
 * @param {Model} model @param {string} elementId @param {string} sid @param {{faults?: string[]}} [opts]
 */
export function compositeBehavior(model, elementId, sid, opts = {}) {
  const s = model.entities.get(sid);
  if (!s || s.kind !== 'scenario') throw new Error(`"${sid}" is not a scenario in this model.`);
  const list = strs(s.data.behaviors);
  const inside = list.filter((b) => { const sub = model.entities.get(b)?.data.subject; return typeof sub === 'string' && within(model, sub, elementId); });
  const others = list.filter((b) => !inside.includes(b));
  const input = engineInput(model, sid, opts.faults);
  const scenarioInputs = [...input.scenario.steps.map((/** @type {any} */ x) => x.event), ...input.faults.filter((/** @type {any} */ f) => f.kind === 'inject-event').map((/** @type {any} */ f) => f.event)];
  const insideEvents = new Set(inside.flatMap((b) => [...eventsOf(model, b)]));
  const outsideEvents = new Set([...others.flatMap((b) => [...eventsOf(model, b)]), ...scenarioInputs]);
  const hidden = sorted([...insideEvents].filter((e) => !outsideEvents.has(e)));
  const trace = runEngine(input);
  const r = call('engine.boundary', { trace, hidden });
  if (!r.ok) throw new Error(r.error);
  return { element: elementId, scenario: sid, members: inside, environment: others, hidden, strength: 'exact', trace, boundary: r.value.steps, hiddenSteps: r.value.hidden };
}

/**
 * The scenarios a refinement check of an abstraction runs: the listed ones, else every scenario that runs the
 * abstraction, else (an abstraction no scenario runs) every scenario that runs all of its members.
 * @param {Model} model @param {string} aid @param {string[]} [listed]
 */
export function drivingScenarios(model, aid, listed) {
  if (listed && listed.length) return listed;
  const all = model.byKind.scenario ?? [];
  const running = all.filter((s) => strs(s.data.behaviors).includes(aid)).map((s) => s.id);
  if (running.length) return running;
  const members = membersOf(model, aid);
  return all.filter((s) => members.length > 0 && members.every((m) => strs(s.data.behaviors).includes(m))).map((s) => s.id);
}

/**
 * The pairs of boundary events whose simultaneous deliveries commute (WG-5734): two different events no running
 * machine consumes both of. A delivery changes only the machines that consume it, so two pending deliveries at one
 * time to disjoint sets of machines give the same configuration in either order; the boundary traces of the
 * abstraction and of its members are compared up to the order of such steps. The region counts as one machine:
 * whatever the abstraction or any of its members consumes. `dependent` names pairs to treat as dependent anyway
 * (a negative run that shows the comparison can fail).
 * @param {Model} model @param {string} aid @param {string[]} behaviors every behaviour of either run
 * @param {string[]} hidden @param {string[]} [inputs] events the scenario or its faults inject
 * @param {string[][]} [dependent]
 * @returns {[string, string][]}
 */
export function independentEvents(model, aid, behaviors, hidden, inputs = [], dependent = []) {
  const region = new Set([aid, ...membersOf(model, aid), ...membersOf(model, aid, { finest: true }), ...collectAbstractions(model, aid)]);
  /** @type {Set<string>[]} */
  const consumers = [];
  const regionIn = new Set();
  for (const b of uniq(behaviors)) {
    const a = alphabetOf(model, b);
    if (region.has(b)) for (const e of a.inputs) regionIn.add(e);
    else consumers.push(a.inputs);
  }
  consumers.push(regionIn);
  const hide = new Set(hidden);
  const events = sorted([...uniq(behaviors).flatMap((b) => [...eventsOf(model, b)]), ...inputs]).filter((e) => !hide.has(e));
  const forced = new Set(dependent.filter((d) => Array.isArray(d) && d.length === 2).flatMap(([x, y]) => [`${x} ${y}`, `${y} ${x}`]));
  /** @type {[string, string][]} */
  const out = [];
  for (let i = 0; i < events.length; i++) {
    for (let j = i + 1; j < events.length; j++) {
      const x = events[i], y = events[j];
      if (forced.has(`${x} ${y}`)) continue;
      if (consumers.some((c) => c.has(x) && c.has(y))) continue;
      out.push([x, y]);
    }
  }
  return out;
}

/**
 * Check a declared abstraction against the composition of its members, in each driving scenario: run the
 * scenario with the region at the abstraction and at its members (or `finest`: the members of member
 * abstractions too), hide the members' internal events and compare the two boundary traces in Lean
 * (`engine.refineBoundary`): equal events, kinds and payloads at times related by the time scale, the same
 * outcome, and the same final configuration of every machine outside the region. The result is a step
 * correspondence per scenario (the certificate) or the first boundary counterexample.
 *
 * Strength (docs/composition.md, "Strength"): `conservative` when every run agrees (a declared abstraction shown
 * to be refined on these runs), `incomplete` when a member of the region has no machine in the run, a fault had
 * to be left out, or no scenario could be run.
 * Simultaneous boundary steps of events no machine consumes both of may appear in either order (`independentEvents`):
 * the comparison is up to their commutation, and each run says which comparison certified it (`sequence` or
 * `commutation`). `dependent` treats listed pairs as dependent. With `explore`, each scenario is also explored over
 * every interleaving, fault mask and draw (`engine.refineExplore`, sound by `explore_holds` in
 * formal/Exegra/BoundaryExplore.lean): every boundary trace of the members must be one of the abstraction with the
 * same faults; the strength is then `explored` when every exploration completes with a certificate.
 * @param {Model} model @param {string} aid
 * @param {{scenarios?: string[], finest?: boolean, faults?: string[], perLevelFaults?: boolean, dependent?: string[][], explore?: {bound?: number, maxStates?: number}|boolean}} [opts]
 */
export function checkAbstraction(model, aid, opts = {}) {
  const a = abstractionOf(model, aid);
  if (!a) throw new Error(`"${aid}" is not a behavior that declares an abstraction ("abstracts").`);
  const level = opts.finest ? 'finest' : 'members';
  const members = opts.finest ? membersOf(model, aid, { finest: true }) : a.members;
  const scenarios = drivingScenarios(model, aid, opts.scenarios);
  /** @type {any[]} */
  const runs = [];
  /** @type {string[]} */
  const notes = [];
  /** @type {any} */
  let counterexample = null;
  for (const sid of scenarios) {
    const sc = model.entities.get(sid);
    if (!sc || sc.kind !== 'scenario') { notes.push(`"${sid}" is not a scenario.`); continue; }
    let abs, con;
    try {
      abs = behaviorsAtLevels(model, sid, { [aid]: 'abstract' }, opts.faults);
      con = behaviorsAtLevels(model, sid, { [aid]: level }, opts.faults);
    } catch (e) { notes.push(/** @type {Error} */ (e).message); continue; }
    const others = abs.behaviors.filter((b) => b !== aid);
    // Normally a fault that acts at one level only is left out of both runs; a negative run (perLevelFaults) applies
    // each fault at whichever level has its transition, to show that the check can fail.
    const faults = abs.faults.filter((f) => con.faults.includes(f));
    const dropped = opts.perLevelFaults ? [] : uniq([...abs.droppedFaults, ...con.droppedFaults, ...abs.faults.filter((f) => !con.faults.includes(f)), ...con.faults.filter((f) => !abs.faults.includes(f))]);
    let ai, ci;
    try {
      ai = inputWith(model, sid, abs.behaviors, opts.perLevelFaults ? abs.faults : faults);
      ci = inputWith(model, sid, con.behaviors, opts.perLevelFaults ? con.faults : faults);
    } catch (e) { notes.push(`Scenario "${sid}": ${/** @type {Error} */ (e).message}`); continue; }
    const inputs = [...ai.scenario.steps.map((/** @type {any} */ x) => x.event), ...ai.faults.filter((/** @type {any} */ f) => f.kind === 'inject-event').map((/** @type {any} */ f) => f.event)];
    const hidden = hiddenFor(model, aid, members, others, inputs);
    const independent = independentEvents(model, aid, [...abs.behaviors, ...con.behaviors], hidden, inputs, opts.dependent ?? []);
    const r = call('engine.refineBoundary', { abstract: ai, concrete: ci, hidden, timeScale: a.timeScale, environment: others, independent });
    if (!r.ok) { notes.push(`Scenario "${sid}" could not be compared: ${r.error}`); continue; }
    /** @type {any} */
    let explored = null;
    if (opts.explore) {
      const ex = typeof opts.explore === 'object' ? opts.explore : {};
      const x = call('engine.refineExplore', { abstract: ai, concrete: ci, hidden, timeScale: a.timeScale, bound: ex.bound ?? 64, maxStates: ex.maxStates ?? 20000 });
      explored = x.ok ? x.value : { verdict: 'incomplete', reason: x.error };
    }
    const regionEls = regionOf(model, aid);
    // An element of the region is covered by a running machine that describes it, or by a running abstraction whose region holds it.
    const covered = new Set(con.behaviors.flatMap((b) => (abstractionOf(model, b) ? regionOf(model, b) : [model.entities.get(b)?.data.subject])));
    // Opaque: an element of the region, or a leaf element inside the abstraction's subject, that no running machine covers.
    const sub = model.entities.get(aid)?.data.subject;
    const leaves = typeof sub === 'string' ? descendantsOf(model, sub).filter((c) => !childrenOf(model, c.id).length).map((c) => c.id) : [];
    const opaque = sorted([...regionEls, ...leaves]).filter((el) => !covered.has(el));
    const run = { scenario: sid, abstraction: aid, abstractBehaviors: abs.behaviors, concreteBehaviors: con.behaviors, faults, droppedFaults: dropped, hidden, opaque, independent: independent.length, ...r.value, ...(explored ? { explored } : {}) };
    runs.push(run);
    if (r.value.verdict === 'counterexample' && !counterexample) counterexample = run;
    else if (explored?.verdict === 'counterexample' && !counterexample) counterexample = { ...run, verdict: 'counterexample', reason: 'interleaving' };
  }
  for (const r of runs) if (r.verdict === 'certificate' && !r.abstract.boundarySteps) notes.push(`Scenario "${r.scenario}" delivers no event in either run, so it checks nothing.`);
  const incomplete = !runs.length || notes.length > 0 || runs.some((r) => r.droppedFaults.length || r.opaque.length);
  const verdict = counterexample ? 'counterexample' : runs.length ? 'certificate' : 'unchecked';
  // A counterexample refutes the abstraction: it has no strength.
  const allExplored = opts.explore && runs.length > 0 && runs.every((r) => r.explored?.verdict === 'certificate');
  const strength = verdict === 'counterexample' ? null : verdict === 'certificate' && !incomplete ? (allExplored ? 'explored' : 'conservative') : 'incomplete';
  return {
    abstraction: aid, subject: model.entities.get(aid)?.data.subject ?? null, members, level, region: regionOf(model, aid),
    timeScale: a.timeScale, verdict, strength, runs, notes, counterexample,
  };
}

/**
 * A one-line account of a counterexample run of checkAbstraction.
 * @param {any} run
 */
export function describeCounterexample(run) {
  const show = (/** @type {any} */ s) => (s ? `${s.kind} ${s.event} at t=${s.time} ${JSON.stringify(s.payload)} (step ${s.index})` : 'nothing');
  if (run.reason === 'outcome') return `In scenario "${run.scenario}" the boundary traces agree, but the abstract run ends ${run.abstract?.outcome ?? '?'} and the members' run ${run.concrete?.outcome ?? '?'}.`;
  if (run.reason === 'interleaving') {
    const ex = run.explored ?? {};
    const shown = (ex.boundary ?? []).map((/** @type {any} */ o) => `${o.event}@${o.time}`).join(', ');
    return `In scenario "${run.scenario}" the scripted runs agree, but another interleaving of the members${ex.activeFaults?.length ? ` (faults ${ex.activeFaults.join(', ')})` : ''} shows the boundary trace [${shown}], which no run of the abstraction "${run.abstraction}" shows (picks ${(ex.run?.picks ?? []).join(',')}).`;
  }
  if (run.reason === 'environment') return `In scenario "${run.scenario}" the boundary traces agree, but machine "${run.machine}" outside the region ends in another configuration.`;
  const ends = (/** @type {any} */ side, /** @type {any} */ step) => (step ? '' : ` (their run ended ${side?.outcome ?? '?'} after ${side?.steps ?? '?'} steps)`);
  return `In scenario "${run.scenario}", boundary step ${run.at} differs (${run.reason}): the abstraction "${run.abstraction}" gives ${show(run.abstractStep)}${ends(run.abstract, run.abstractStep)}, the members give ${show(run.concreteStep)}${ends(run.concrete, run.concreteStep)}.`;
}

// ---------------------------------------------------------------------------
// Order independence (I2)
// ---------------------------------------------------------------------------

/**
 * The orders a check tries for a list of n behaviours: reversed, and every rotation, without repeats.
 * @param {number} n @returns {number[][]}
 */
export function orders(n) {
  const id = [...Array(n).keys()];
  const out = [id.slice().reverse()];
  for (let k = 1; k < n; k++) out.push([...id.slice(k), ...id.slice(0, k)]);
  const seen = new Set([id.join(',')]);
  return out.filter((p) => { const key = p.join(','); if (seen.has(key)) return false; seen.add(key); return true; });
}

/**
 * A trace written so that the order in which behaviours are listed cannot show: per step its time, kind, event,
 * payload and the transitions that fired (sorted), and the final configuration of every machine.
 * @param {any} trace
 */
export function canonicalTrace(trace) {
  const sortKeys = (/** @type {any} */ v) => JSON.stringify(v, (_k, x) => (x && typeof x === 'object' && !Array.isArray(x) ? Object.fromEntries(Object.keys(x).sort().map((k) => [k, x[k]])) : x));
  return {
    outcome: trace.outcome,
    steps: (trace.steps ?? []).map((/** @type {any} */ s) => `${s.time}|${s.kind}|${s.event?.id}|${sortKeys(s.event?.payload ?? {})}|${(s.fired ?? []).map((/** @type {any} */ f) => f.transition).sort().join(',')}`),
    final: sortKeys(trace.final?.machines ?? {}),
  };
}

/**
 * Run a scenario with its behaviours listed in other orders and compare: the verdict of every invariant and
 * temporal claim that lists the scenario (`verdicts`, a function from a trace to {claimId: verdict}) for the
 * scenario's own fault set and for each extra fault set given, and the traces up to the order of behaviours.
 * The kernel's composition is the list of machines of one input; `invariant_rename` (formal/Exegra/Core/
 * BehavRename.lean) proves that the verdict of a safety property does not depend on that order in the
 * calculus's relation; this is the empirical check on the scheduler's runs.
 * @param {Model} model @param {string} sid @param {(trace: any) => Record<string, string>} verdicts
 * @param {{faultSets?: string[][]}} [opts]
 */
export function orderIndependence(model, sid, verdicts, opts = {}) {
  const s = model.entities.get(sid);
  if (!s || s.kind !== 'scenario') throw new Error(`"${sid}" is not a scenario in this model.`);
  const list = strs(s.data.behaviors);
  const sets = [null, ...(opts.faultSets ?? [])];
  /** @type {any[]} */
  const differences = [];
  let runs = 0, traceDifferences = 0;
  for (const faults of sets) {
    const base = engineInput(model, sid, faults ?? undefined);
    const t0 = runEngine(base);
    const v0 = verdicts(t0);
    const c0 = JSON.stringify(canonicalTrace(t0));
    for (const p of orders(list.length)) {
      const input = { ...base, behaviors: p.map((i) => base.behaviors[i]) };
      const t = runEngine(input);
      runs++;
      const v = verdicts(t);
      const changed = Object.keys({ ...v0, ...v }).filter((k) => v0[k] !== v[k]);
      const sameTrace = JSON.stringify(canonicalTrace(t)) === c0;
      if (!sameTrace) traceDifferences++;
      if (changed.length) differences.push({ order: p.map((i) => list[i]), faults: faults ?? strs(s.data.faults), claims: changed.map((k) => ({ claim: k, original: v0[k] ?? null, reordered: v[k] ?? null })) });
    }
  }
  return { scenario: sid, behaviors: list, orders: runs, verdictsIndependent: differences.length === 0, traceDifferences, differences };
}

// ---------------------------------------------------------------------------
// Claim transfer (I6)
// ---------------------------------------------------------------------------

const SAFETY_METHODS = new Set(['never', 'precedes', 'state-invariant']);

/**
 * Whether a claim established at one level holds at another, by the preservation rules (docs/composition.md,
 * "Claim transfer"):
 * - safety over the boundary alphabet transfers down a refinement (from a declared abstraction to its members)
 *   when the refinement check gives a certificate;
 * - for a derived composite (exact) the boundary traces are equal, so such a claim transfers both ways;
 * - liveness transfers only under a declared fairness hypothesis, and never from finite runs;
 * - everything else is not transferred, and says why.
 * @param {Model} model @param {string} claimId @param {string} aid @param {{refinement?: any, sourceStatus?: string}} [opts]
 */
export function transferClaim(model, claimId, aid, opts = {}) {
  const claim = model.entities.get(claimId);
  if (!claim || claim.kind !== 'claim') throw new Error(`"${claimId}" is not a claim.`);
  const ev = obj(claim.data.evaluate) ?? {};
  const method = typeof ev.method === 'string' ? ev.method : null;
  const base = { claim: claimId, abstraction: aid, method, direction: 'down' };
  if (method === 'liveness' || method === 'eventually') {
    const fair = strs(claim.data.assumptions).filter((x) => obj(model.entities.get(x)?.data.fairness));
    return { ...base, transferred: false, rule: null, reason: fair.length
      ? `A liveness claim needs its fairness hypothesis (${fair.join(', ')}) re-established for the members: weak fairness of the abstraction's transitions is not weak fairness of the members' transitions, and trace inclusion on finite runs does not preserve liveness. It is not transferred.`
      : `"${claimId}" is a liveness property (${method}), and liveness never transfers along a refinement without a declared fairness hypothesis: trace inclusion on the boundary preserves safety only.` };
  }
  if (!method || !SAFETY_METHODS.has(method)) return { ...base, transferred: false, rule: null, reason: `Method "${method}" is not a safety property over traces, so no preservation rule applies.` };
  const sigma = eventsOf(model, aid);
  /** @type {string[]} */
  const reads = [];
  if (method === 'state-invariant' && typeof ev.expr === 'string') {
    const p = parseExpr(ev.expr);
    if (p.ok) for (const path of exprRefs(p.ast)) if (path.length === 2 && path[0] === aid) reads.push(path.join('.'));
  }
  const matchers = [ev.occurs, ev.first, ev.then].filter(obj);
  // Events internal to the members (theirs, not the abstraction's) do not exist at the abstraction's level.
  const internal = new Set(membersOf(model, aid, { finest: true }).flatMap((m) => [...eventsOf(model, m)]).filter((e) => !sigma.has(e)));
  const offBoundary = matchers.filter((m) => (typeof m.event === 'string' && internal.has(m.event)) || (typeof m.transition === 'string' && model.entities.get(m.transition)?.owner === aid));
  if (reads.length) return { ...base, transferred: false, rule: null, reason: `The claim reads the abstraction's own state (${reads.join(', ')}), which the members do not have: it is not over the boundary alphabet, so it is not expressible at the members' level.` };
  if (offBoundary.length) return { ...base, transferred: false, rule: null, reason: 'The claim names an occurrence that is not on the boundary (a transition of the abstraction, or an event internal to its members), so it is not expressible at the other level.' };
  if (opts.sourceStatus && !['verified', 'proved', 'model-holds'].includes(opts.sourceStatus)) {
    return { ...base, transferred: false, rule: null, reason: `The claim is ${opts.sourceStatus} at the abstraction's level, so there is nothing to transfer.` };
  }
  // The refinement is checked on the claim's own scenarios that run the abstraction.
  const claimScenarios = strs(typeof ev.scenarios === 'string' ? [ev.scenarios] : ev.scenarios);
  const running = claimScenarios.filter((s) => strs(model.entities.get(s)?.data.behaviors).includes(aid));
  if (!running.length) return { ...base, transferred: false, rule: null, reason: `None of the claim's scenarios runs "${aid}", so there is no refinement to transfer it along.` };
  const ref = opts.refinement ?? checkAbstraction(model, aid, { scenarios: running });
  if (ref.verdict !== 'certificate') {
    return { ...base, transferred: false, rule: null, refinement: ref.verdict, reason: ref.verdict === 'counterexample'
      ? `The refinement of "${aid}" by its members fails (${describeCounterexample(ref.counterexample)}), so safety established on "${aid}" says nothing about the members.`
      : `The refinement of "${aid}" by its members was not checked (${ref.notes.join(' ') || 'no scenario runs it'}), so the claim is not transferred.` };
  }
  const certified = ref.runs.filter((/** @type {any} */ r) => r.verdict === 'certificate' && !r.droppedFaults.length && !r.opaque.length).map((/** @type {any} */ r) => r.scenario);
  const excluded = claimScenarios.filter((s) => !certified.includes(s));
  if (!certified.length) return { ...base, transferred: false, rule: null, refinement: ref.verdict, reason: `The refinement of "${aid}" is only ${ref.strength} on the claim's scenarios (${ref.runs.map((/** @type {any} */ r) => r.scenario).join(', ')}), so the claim is not transferred.` };
  return { ...base, transferred: true, rule: 'safety-down-refinement', refinement: ref.verdict, strength: ref.strength, scenarios: certified, excluded,
    reason: `Safety over the boundary of "${aid}" transfers down a refinement: in ${certified.join(', ')} the members' boundary traces agree with the abstraction's, so the claim holds there with ${membersOf(model, aid).join(', ')} in place of "${aid}".${excluded.length ? ` Not transferred for ${excluded.join(', ')}, where the refinement was not certified (a fault acts at one level only, a member is opaque, or the scenario does not run "${aid}").` : ''}` };
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

/**
 * Diagnostics of interfaces, abstractions, cuts and alternative machines.
 * @param {Model} model
 * @returns {Diagnostic[]}
 */
export function checkComposition(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {'error'|'warning'|'info'} severity @param {string} code @param {Entity} entity @param {string} message @param {(string|number)[]} [sub] */
  const report = (severity, code, entity, message, sub) => {
    out.push({ code, severity, message, entityId: entity.id, loc: entity.loc, path: sub ? [...entity.path, ...sub] : entity.path });
  };
  const behaviorIds = new Set((model.byKind.behavior ?? []).map((b) => b.id));
  const anyInterface = ['component', 'port'].some((k) => (model.byKind[k] ?? []).some((e) => declaredInterface(model, e.id)));

  // Declared interfaces: observables name real state; the members' boundary events are all declared.
  for (const k of ['component', 'port']) {
    for (const e of model.byKind[k] ?? []) {
      const i = declaredInterface(model, e.id);
      if (!i) continue;
      const element = k === 'port' ? /** @type {string} */ (e.owner) : e.id;
      i.observables.forEach((o, n) => {
        const [b, v, ...rest] = o.split('.');
        const be = model.entities.get(b);
        const vars = Array.isArray(be?.data.variables) ? be.data.variables.map((/** @type {any} */ x) => x?.name) : [];
        if (rest.length || !be || be.kind !== 'behavior' || (v !== 'state' && !vars.includes(v))) {
          report('error', 'interface.observable-unknown', e, `The interface of "${e.id}" exports "${o}", which is not "<behavior>.<variable>" or "<behavior>.state" of a behavior.`, ['interface', 'observables', n]);
        } else if (typeof be.data.subject !== 'string' || !within(model, be.data.subject, element)) {
          report('error', 'interface.observable-foreign', e, `The interface of "${e.id}" exports "${o}", but behavior "${b}" describes "${be.data.subject}", which is not "${element}" or inside it.`, ['interface', 'observables', n]);
        }
      });
      if (k === 'component') {
        const inf = inferredInterface(model, e.id);
        const mi = inf.inputs.filter((x) => !i.inputs.includes(x));
        const mo = inf.outputs.filter((x) => !i.outputs.includes(x));
        if (mi.length) report('error', 'interface.undeclared-input', e, `The members of "${e.id}" consume ${mi.map((x) => `"${x}"`).join(', ')} from outside it, but its declared interface does not list ${mi.length === 1 ? 'it' : 'them'} as inputs.`, ['interface', 'inputs']);
        if (mo.length) report('error', 'interface.undeclared-output', e, `The members of "${e.id}" emit ${mo.map((x) => `"${x}"`).join(', ')} to outside it, but its declared interface does not list ${mo.length === 1 ? 'it' : 'them'} as outputs.`, ['interface', 'outputs']);
      }
    }
  }

  // Cross-element state reads go through exported observables.
  for (const r of crossReads(model)) {
    if (!r.unexportedBy.length) continue;
    const t = model.entities.get(r.transition);
    if (!t) continue;
    report('error', 'behavior.reads-unexported', t, `Transition "${r.transition}" of "${r.reader}" (element "${r.readerElement}") reads "${r.observable}" of element "${r.targetElement}", which the interface of ${r.unexportedBy.map((x) => `"${x}"`).join(', ')} does not export as an observable.`);
  }

  // Every event belongs to an interface, once the specification declares interfaces at all.
  if (anyInterface) {
    for (const [ev, owners] of eventInterfaces(model)) {
      if (owners.length) continue;
      const e = model.entities.get(ev);
      if (e) report('error', 'event.no-interface', e, `Event "${ev}" belongs to no interface: no element or port declares it, no behavior consumes or emits it, and it names no producer (producedBy).`);
    }
  }

  // Declared abstractions.
  for (const b of model.byKind.behavior ?? []) {
    const a = abstractionOf(model, b);
    if (!a) continue;
    if (!a.members.length) { report('error', 'behavior.abstraction-members', b, `Behavior "${b.id}" declares an abstraction with no members.`, ['abstracts', 'members']); continue; }
    a.members.forEach((m, n) => {
      if (!behaviorIds.has(m)) report('error', 'behavior.abstraction-members', b, `The abstraction "${b.id}" lists "${m}", which is not a behavior.`, ['abstracts', 'members', n]);
      else if (m === b.id) report('error', 'behavior.abstraction-members', b, `The abstraction "${b.id}" lists itself as a member.`, ['abstracts', 'members', n]);
    });
    if (new Set(a.members).size !== a.members.length) report('error', 'behavior.abstraction-members', b, `The abstraction "${b.id}" lists a member twice.`, ['abstracts', 'members']);
    // Cycles through members.
    /** @type {Set<string>} */
    const seen = new Set();
    /** @param {string} x @returns {boolean} */
    const reaches = (x) => {
      if (x === b.id) return true;
      if (seen.has(x)) return false;
      seen.add(x);
      return (abstractionOf(model, x)?.members ?? []).some(reaches);
    };
    if (a.members.filter((m) => m !== b.id).some(reaches)) {
      report('error', 'behavior.abstraction-cycle', b, `The abstraction "${b.id}" is among its own members, at some depth.`, ['abstracts', 'members']);
    }
    // The region: the elements of the finest members (an abstraction's members may be abstractions themselves).
    const subjects = regionOf(model, b.id);
    const sub = b.data.subject;
    if (typeof sub === 'string' && subjects.length && !subjects.includes(sub) && !subjects.every((s) => within(model, s, sub))) {
      report('error', 'behavior.abstraction-subject', b, `The abstraction "${b.id}" describes "${sub}", which is neither one of the elements its members describe (${subjects.join(', ')}) nor an element that contains them all.`, ['subject']);
    }
    if (a.hide) {
      const own = eventsOf(model, b.id);
      const memberEvents = new Set(a.members.flatMap((m) => [...eventsOf(model, m)]));
      a.hide.forEach((ev, n) => {
        if (own.has(ev)) report('error', 'behavior.abstraction-hides-boundary', b, `The abstraction "${b.id}" hides "${ev}", which is an event of its own boundary.`, ['abstracts', 'hide', n]);
        else if (!memberEvents.has(ev)) report('error', 'behavior.abstraction-hides-unknown', b, `The abstraction "${b.id}" hides "${ev}", which no member consumes or emits.`, ['abstracts', 'hide', n]);
      });
    }
  }

  // Scenario cuts: declared regions agree with the listed behaviours; no region runs at two levels at once.
  for (const s of model.byKind.scenario ?? []) {
    const listed = strs(s.data.behaviors);
    const cut = obj(s.data.cut);
    for (const b of model.byKind.behavior ?? []) {
      if (!abstractionOf(model, b) || !listed.includes(b.id)) continue;
      const both = membersOf(model, b.id, { finest: true }).concat(collectAbstractions(model, b.id)).filter((m) => listed.includes(m));
      if (both.length) report('error', 'scenario.levels-overlap', s, `Scenario "${s.id}" runs the abstraction "${b.id}" together with ${both.map((x) => `"${x}"`).join(', ')}, which it stands for: one region would run at two levels at once.`, ['behaviors']);
    }
    if (!cut) continue;
    (Array.isArray(cut.regions) ? cut.regions : []).forEach((/** @type {any} */ r, /** @type {number} */ n) => {
      const a = typeof r?.abstraction === 'string' ? abstractionOf(model, r.abstraction) : null;
      if (!a) { report('error', 'scenario.cut-region', s, `Region ${n} of the cut of "${s.id}" names "${r?.abstraction}", which is not a behavior that declares an abstraction.`, ['cut', 'regions', n]); return; }
      const members = membersOf(model, a.behavior);
      if (r.level === 'members' ? (listed.includes(a.behavior) || !members.every((m) => listed.includes(m))) : !listed.includes(a.behavior)) {
        report('error', 'scenario.cut-region', s, `The cut of "${s.id}" runs region "${a.behavior}" at its ${r.level === 'members' ? 'members' : 'abstract'} level, but the scenario lists ${r.level === 'members' ? `${listed.includes(a.behavior) ? `"${a.behavior}"` : `not every member (${members.filter((m) => !listed.includes(m)).join(', ')})`}` : `no "${a.behavior}"`}.`, ['cut', 'regions', n]);
      }
    });
    (Array.isArray(cut.environment) ? cut.environment : []).forEach((/** @type {any} */ e, /** @type {number} */ n) => {
      const el = typeof e?.element === 'string' ? model.entities.get(e.element) : null;
      if (!el || el.kind !== 'component') report('error', 'scenario.environment-element', s, `Environment assumption ${n} of "${s.id}" names "${e?.element}", which is not a component.`, ['cut', 'environment', n]);
      else if (listed.some((b) => model.entities.get(b)?.data.subject === el.id)) report('error', 'scenario.environment-element', s, `Environment assumption ${n} of "${s.id}" stands for "${el.id}", which the scenario runs a behavior of.`, ['cut', 'environment', n]);
    });
  }

  // Same-subject alternative machines are a gap until they are related by a checked refinement.
  for (const p of alternativeMachines(model)) {
    const e = /** @type {Entity} */ (model.entities.get(p.b));
    report('info', 'gap.alternative-machines', e, `Behaviors "${p.a}" and "${p.b}" both describe "${p.subject}" and consume ${p.shared.map((x) => `"${x}"`).join(', ')}, but no scenario runs them together and neither is declared an abstraction of the other: they are alternative machines of one element at one level.`);
  }
  return out;
}
