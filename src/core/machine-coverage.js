// Transition and guard coverage of shipped implementation machines (WG-4965). docs/coverage.md.
//
// For each implementation-level behavior whose realisation is shipped (realisation.js), the coverage items are its
// transitions and, for each guarded transition, its two guard outcomes: true (the transition fires) and false (the
// event is delivered in its source state and the guard does not hold). Which items the specification's own
// scenarios exercise is read from their traces (engine.js). For every item they leave out, a bounded breadth-first
// search over sequences of the machine's input events, with representative payloads from the declared types and
// waits drawn from the machine's time thresholds, looks for a sequence that reaches it; the shortest found are
// returned as generated scenarios, which coverageOperations turns into apply operations.
//
// A transition that neither the scenarios nor the search reach is a finding, machine.transition-unreachable: a
// warning, an error when system.generation is set. The search is bounded (by the number of actions and of engine
// runs), so a finding says "within the bound", and says so when the search exhausted every state it could reach.
// Everything the report claims as covered was observed in a trace of the engine.

import { effectiveRealisation } from './realisation.js';
import { engineInput, runEngine } from './engine.js';
import { parseExpr, exprRefs } from './expr.js';
import { typeStructure } from './codegen-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {{at: number, event: string, payload: Record<string, any>}} Step */

/** The tag a generated coverage scenario carries. */
export const COVERAGE_TAG = 'generated-coverage';

/** Default bounds of the search. */
export const DEFAULT_BOUND = 12;
export const DEFAULT_MAX_RUNS = 5000;

const INT_NAMES = ['u8', 'u16', 'u32', 'u64', 'i32', 'i64', 'timestamp', 'duration', 'number'];

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} t */
const hasGuard = (t) => typeof t.data.guard === 'string' && t.data.guard.trim() !== '';

/**
 * The implementation-level machines whose realisation is shipped, in declaration order.
 * @param {Model} model @returns {Entity[]}
 */
export function shippedMachines(model) {
  return (model.byKind.behavior ?? []).filter((b) => b.data.level === 'implementation' && effectiveRealisation(model, b) === 'shipped');
}

/**
 * The coverage items of a machine: "t:<transition>" for each transition that is not faultOnly, and
 * "g:<transition>:true" / "g:<transition>:false" for each guarded one.
 * @param {Model} model @param {Entity} b
 */
export function machineItems(model, b) {
  const transitions = (model.byKind.transition ?? []).filter((t) => t.owner === b.id && t.data.faultOnly !== true);
  /** @type {string[]} */
  const items = [];
  for (const t of transitions) {
    items.push(`t:${t.id}`);
    if (hasGuard(t)) items.push(`g:${t.id}:true`, `g:${t.id}:false`);
  }
  return { transitions, items };
}

/**
 * The items of machine `b` a trace exercises. A transition fires (its item, and its guard true when it has one);
 * the guarded transitions of the same state and event declared before it were tried and false; an event ignored
 * with reason guard-false had every considered guard false.
 * @param {Entity[]} transitions the machine's transitions in declaration order @param {string} bid @param {any} trace
 * @returns {Set<string>}
 */
export function exercisedItems(transitions, bid, trace) {
  /** @type {Set<string>} */
  const out = new Set();
  const byId = new Map(transitions.map((t) => [t.id, t]));
  for (const step of list(trace?.steps)) {
    if (step.kind !== 'deliver') continue;
    const eventId = step.event?.id;
    for (const f of list(step.fired)) {
      if (f.behavior !== bid) continue;
      const t = byId.get(f.transition);
      if (!t) continue;
      out.add(`t:${t.id}`);
      if (hasGuard(t)) out.add(`g:${t.id}:true`);
      const from = typeof f.from === 'string' ? f.from : t.data.from;
      for (const o of transitions) {
        if (o === t) break;
        if (o.data.from === from && o.data.on === eventId && hasGuard(o)) out.add(`g:${o.id}:false`);
      }
    }
    for (const i of list(step.ignored)) {
      if (i.behavior !== bid || i.reason !== 'guard-false') continue;
      for (const id of list(i.considered)) {
        const o = byId.get(id);
        if (o && hasGuard(o)) out.add(`g:${o.id}:false`);
      }
    }
  }
  return out;
}

/** The literals of an expression of the behavior language. @param {any} src @returns {any[]} */
function literalsOf(src) {
  if (typeof src !== 'string') return [];
  const p = parseExpr(src);
  if (!p.ok) return [];
  /** @type {any[]} */
  const out = [];
  /** @param {any} n */
  const walk = (n) => {
    if (!n) return;
    if (n.t === 'lit') out.push(n.v);
    else if (n.t === 'un') walk(n.a);
    else if (n.t === 'bin') { walk(n.a); walk(n.b); }
  };
  walk(p.ast);
  return out;
}

/** Whether an expression reads `time`. @param {any} src */
function readsTime(src) {
  if (typeof src !== 'string') return false;
  const p = parseExpr(src);
  return p.ok && exprRefs(p.ast).some((path) => path.length === 1 && path[0] === 'time');
}

/**
 * The class of a payload field's values: bool, number, string, an enum's values, or other.
 * @param {Model} model @param {any} field
 * @returns {{optional: boolean, cls: 'bool'|'number'|'string'|'enum'|'other', values?: string[]}}
 */
function fieldClass(model, field) {
  let optional = field?.optional === true;
  let t = typeof field?.type === 'string' ? typeStructure(model, field.type) : undefined;
  if (typeof field?.type === 'string' && INT_NAMES.includes(field.type.trim())) return { optional, cls: 'number' };
  if (t && t.k === 'option') { optional = true; t = /** @type {any} */ (t).of; }
  const any = /** @type {any} */ (t);
  if (!any) return { optional, cls: 'other' };
  if (any.k === 'prim') {
    if (any.name === 'bool') return { optional, cls: 'bool' };
    if (INT_NAMES.includes(any.name)) return { optional, cls: 'number' };
    if (any.name === 'string' || any.name === 'uuid') return { optional, cls: 'string' };
  }
  if (any.k === 'alias') {
    const r = String(any.repr ?? '');
    if (INT_NAMES.includes(r)) return { optional, cls: 'number' };
    if (r === 'string' || r === 'uuid') return { optional, cls: 'string' };
  }
  if (any.k === 'enum' && Array.isArray(any.values)) return { optional, cls: 'enum', values: any.values };
  return { optional, cls: 'other' };
}

/** Distinct values in first-seen order (by JSON). @param {any[]} xs */
function distinct(xs) {
  const seen = new Set();
  return xs.filter((x) => {
    const k = JSON.stringify(x);
    if (x === undefined || seen.has(k)) return false;
    seen.add(k);
    return true;
  });
}

/**
 * Everything the search needs about one machine: the scenario template (time unit, routes, step limit), the input
 * events with their payload variants, the waits, and the engine input to fill with steps.
 * @param {Model} model @param {Entity} b @param {Entity[]} transitions @param {Entity[]} scenarios the scenarios that run b
 */
function searchSpace(model, b, transitions, scenarios) {
  const get = (/** @type {string} */ id) => model.entities.get(id);
  // Events the machine emits itself (an emit or a timer) arrive through its own effects, not as inputs.
  /** @type {Set<string>} */
  const selfEmitted = new Set();
  for (const t of transitions) for (const fx of list(t.data.effects)) if (isObj(fx) && typeof fx.emit === 'string') selfEmitted.add(fx.emit);
  const inputs = distinct(transitions.map((t) => t.data.on)).filter((id) => typeof id === 'string' && get(id)?.kind === 'event' && !selfEmitted.has(id));

  const template = scenarios[0]?.data ?? {};
  // The routes to this machine: the template's, and a route by key for each input event that carries the key.
  /** @type {any[]} */
  const routes = list(template.routes).filter((r) => isObj(r) && r.behavior === b.id).map((r) => ({ ...r }));
  const inst = isObj(b.data.instances) ? b.data.instances : undefined;
  if (inst && typeof inst.key === 'string') {
    for (const ev of inputs) {
      if (routes.some((r) => r.event === ev)) continue;
      if (list(get(ev)?.data.payload).some((f) => f?.name === inst.key)) routes.push({ event: ev, behavior: b.id, by: 'key', field: inst.key });
    }
  }
  // One instance: every key field holds the same value.
  /** @type {Map<string, Set<string>>} */
  const keyFields = new Map();
  for (const r of routes) if (r.by === 'key' && typeof r.field === 'string') keyFields.set(r.event, new Set([...(keyFields.get(r.event) ?? []), r.field]));

  // Values the specification already uses: scenario payloads, guard literals, variable initials.
  /** @type {Map<string, any[]>} */
  const seen = new Map();
  for (const s of model.byKind.scenario ?? []) {
    for (const st of list(s.data.steps)) {
      if (!isObj(st) || !isObj(st.payload)) continue;
      for (const [k, v] of Object.entries(st.payload)) seen.set(`${st.event}.${k}`, [...(seen.get(`${st.event}.${k}`) ?? []), v]);
    }
  }
  const keyValue = (() => {
    for (const [ev, fields] of keyFields) for (const f of fields) { const v = seen.get(`${ev}.${f}`)?.[0]; if (v !== undefined) return v; }
    return 'k1';
  })();
  const guardLits = (/** @type {string} */ ev) => transitions.filter((t) => t.data.on === ev).flatMap((t) => literalsOf(t.data.guard));
  const varInitials = list(b.data.variables).map((v) => v?.initial);

  /** @param {string} ev */
  const payloads = (ev) => {
    const fields = list(get(ev)?.data.payload).filter((f) => isObj(f) && typeof f.name === 'string');
    const lits = guardLits(ev);
    /** @type {{name: string, values: any[]}[]} */
    const cands = fields.map((f) => {
      if (keyFields.get(ev)?.has(f.name)) return { name: f.name, values: [keyValue] };
      const c = fieldClass(model, f);
      const used = seen.get(`${ev}.${f.name}`) ?? [];
      /** @type {any[]} */
      let values;
      if (c.cls === 'bool') values = [...used.filter((v) => typeof v === 'boolean'), true, false];
      else if (c.cls === 'number') {
        const nums = [...used, ...lits, ...varInitials].filter((v) => typeof v === 'number' && Number.isFinite(v));
        values = [...used.filter((v) => typeof v === 'number'), ...nums.flatMap((n) => [n, n + 1, n - 1]), 0, 1, 2].filter((v) => typeof v === 'number' && Number.isInteger(v) && v >= 0);
      } else if (c.cls === 'string') values = [...used.filter((v) => typeof v === 'string'), ...lits.filter((v) => typeof v === 'string'), ...varInitials.filter((v) => typeof v === 'string'), 'a', 'b'];
      else if (c.cls === 'enum') values = [...used, ...(c.values ?? [])];
      else values = used.length ? used : [null];
      values = distinct(values).slice(0, c.cls === 'number' ? 6 : 4);
      if (c.optional) values = distinct([...values.slice(0, 3), null]);
      return { name: f.name, values };
    });
    /** @type {Record<string, any>[]} */
    let out = [];
    const product = cands.reduce((n, c) => n * c.values.length, 1);
    if (product <= 12) {
      out = [{}];
      for (const c of cands) out = out.flatMap((p) => c.values.map((v) => ({ ...p, [c.name]: v })));
    } else {
      const base = Object.fromEntries(cands.map((c) => [c.name, c.values[0]]));
      out = [base, ...cands.flatMap((c) => c.values.slice(1).map((v) => ({ ...base, [c.name]: v })))];
    }
    // The payloads scenarios deliver, with the instance key replaced.
    for (const s of model.byKind.scenario ?? []) for (const st of list(s.data.steps)) {
      if (st?.event !== ev || !isObj(st.payload)) continue;
      const p = { ...st.payload };
      for (const f of keyFields.get(ev) ?? []) p[f] = keyValue;
      out.push(p);
    }
    return distinct(out.map((p) => Object.fromEntries(Object.entries(p).filter(([, v]) => v !== null)))).slice(0, 16);
  };

  // Waits past each time threshold the machine's time-reading expressions name. Waiting for a timer or a delayed
  // event is a separate action of the search (to just after the next thing pending), so their delays are not here.
  /** @type {number[]} */
  const thresholds = [];
  for (const t of transitions) {
    if (readsTime(t.data.guard)) thresholds.push(...literalsOf(t.data.guard).filter((v) => typeof v === 'number'));
    for (const fx of list(t.data.effects)) if (isObj(fx) && 'set' in fx && readsTime(fx.to)) thresholds.push(...literalsOf(fx.to).filter((v) => typeof v === 'number'));
  }
  const waits = distinct(thresholds.filter((n) => Number.isInteger(n) && n >= 1).map((n) => n + 1)).sort((x, y) => x - y).slice(0, 6);

  // The engine input of an empty scenario of this machine alone, with only the events it can meet.
  const id = `cover-${b.id}`;
  /** @type {Record<string, any>} */
  const sdata = { id, name: id, behaviors: [b.id], steps: [], ...(typeof template.timeUnit === 'string' ? { timeUnit: template.timeUnit } : {}), ...(routes.length ? { routes } : {}), ...(template.maxSteps !== undefined ? { maxSteps: template.maxSteps } : {}) };
  const scenarioEntity = /** @type {Entity} */ (/** @type {unknown} */ ({ id, owner: null, kind: 'scenario', data: sdata, path: [], loc: { line: 0, column: 0 } }));
  const entities = new Map(model.entities);
  entities.set(id, scenarioEntity);
  const input = engineInput(/** @type {Model} */ ({ ...model, entities }), id);
  /** @type {Set<string>} */
  const used = new Set(inputs);
  for (const t of transitions) { used.add(t.data.on); for (const fx of list(t.data.effects)) if (isObj(fx) && typeof fx.emit === 'string') used.add(fx.emit); }
  input.events = input.events.filter((/** @type {any} */ e) => used.has(e.id));
  return { inputs: inputs.map((ev) => ({ event: ev, payloads: payloads(ev) })), waits, routes, timeUnit: template.timeUnit, maxSteps: template.maxSteps, input };
}

/**
 * The state a run leaves the machine in at time `at`, for deduplicating the search: the machines' states and
 * variables (a timestamp variable as its age, capped past the longest wait), and what is pending, at its time
 * relative to `at`. With `guardVars`, a coarser key: only the variables guards read, and only which events are
 * pending.
 * @param {any} trace @param {number} at @param {Set<string>} stamps the timestamp variables @param {number} cap
 * @param {Set<string>} [guardVars]
 */
function stateKey(trace, at, stamps, cap, guardVars) {
  let config = trace.initial;
  for (const s of list(trace.steps)) { if (s.time > at) break; config = s.config; }
  /** @type {Record<string, any>} */
  const machines = {};
  for (const [k, m] of Object.entries(config?.machines ?? {})) {
    const mm = /** @type {any} */ (m);
    const vars = Object.fromEntries(Object.entries(mm.vars ?? {}).filter(([n]) => !guardVars || guardVars.has(n)).map(([n, v]) => [n, stamps.has(n) && typeof v === 'number' ? Math.min(cap, at - v) : v]));
    machines[k] = { state: mm.state, vars };
  }
  const pending = list(config?.pending).map((p) => (guardVars ? p.event : [p.event, p.time - at, p.payload]));
  if (guardVars) pending.sort();
  const timers = Object.keys(config?.timers ?? {}).sort();
  return JSON.stringify({ machines, pending, timers });
}

/**
 * Run the steps on the machine's engine input. Null when the engine refuses the input or the run does not end
 * quiescent (an error part-way or the step limit).
 * @param {any} input @param {Step[]} steps
 */
function runSteps(input, steps) {
  try {
    const trace = runEngine({ ...input, scenario: { ...input.scenario, steps } });
    return trace.outcome === 'quiescent' ? trace : null;
  } catch {
    return null;
  }
}

/**
 * The breadth-first search for the items the scenarios leave out, in rounds: first with the first payload of each
 * event and states told apart only by their control state, the variables guards read and which events are pending
 * (so that long sequences are reached early), then with the full state and widening payload choice (the first
 * payload of each event, three, then all). An action is
 * the delivery of an input event one time unit after the last action, or a wait. Each delivery is one engine run of
 * the whole sequence; a run that covers an item still open is kept as a candidate. States are deduplicated within a
 * round (stateKey). Stops when every item is covered, or when a round ends: by exhausting its states, by the bound
 * on actions or by the bound on runs. Records what covered each item in `by`.
 * @param {Entity} b @param {Entity[]} transitions @param {string[]} items @param {any} space
 * @param {Map<string, string>} by @param {{steps: Step[], covers: Set<string>}[]} candidates
 * @param {number} bound @param {number} maxRuns
 * @returns {{runs: number, stoppedBy: 'states'|'bound'|'runs'}}
 */
function search(b, transitions, items, space, by, candidates, bound, maxRuns) {
  const open = () => items.some((it) => !by.has(it));
  let runs = 0;
  /** @type {'states'|'bound'|'runs'} */
  let stoppedBy = 'states';
  if (!open()) return { runs, stoppedBy };
  const stamps = new Set(list(b.data.variables).filter((v) => v?.repr === 'timestamp' || v?.type === 'timestamp').map((v) => v.name));
  const cap = (space.waits.at(-1) ?? 1) + 1;
  const empty = runSteps(space.input, []);
  if (!empty) return { runs, stoppedBy };
  const widest = Math.max(1, ...space.inputs.map((/** @type {any} */ i) => i.payloads.length));
  // The variables guards read: the coarse first round tells states apart by these alone.
  const names = new Set(list(b.data.variables).map((v) => v?.name));
  const guardVars = new Set(transitions.flatMap((t) => {
    const p = typeof t.data.guard === 'string' ? parseExpr(t.data.guard) : undefined;
    return p && p.ok ? exprRefs(p.ast).filter((path) => path.length === 1 && names.has(path[0])).map((path) => path[0]) : [];
  }));
  /** @type {{width: number, coarse: boolean}[]} */
  const rounds = [{ width: 1, coarse: true }, ...[...new Set([1, 3, widest].filter((w) => w <= widest))].map((width) => ({ width, coarse: false }))];
  for (const [round, { width, coarse }] of rounds.entries()) {
    const key = (/** @type {any} */ trace, /** @type {number} */ at) => stateKey(trace, at, stamps, cap, coarse ? guardVars : undefined);
    // Each round may use its share of the runs, and what earlier rounds left: half for the coarse round, the
    // rest split evenly.
    const limit = round === 0 ? Math.ceil(maxRuns / 2) : Math.ceil(maxRuns / 2 + (maxRuns / 2) * (round / (rounds.length - 1)));
    stoppedBy = 'states';
    /** @type {{steps: Step[], at: number, trace: any}[]} */
    let frontier = [{ steps: [], at: 0, trace: empty }];
    const seenKeys = new Set([key(empty, 0)]);
    for (let depth = 0; frontier.length && open(); depth++) {
      if (depth >= bound) { stoppedBy = 'bound'; break; }
      /** @type {{steps: Step[], at: number, trace: any}[]} */
      const next = [];
      for (const node of frontier) {
        if (!open() || runs >= limit) break;
        // A wait: no run, the next input arrives later: past a time threshold, or once the next thing pending
        // (a timer, a delayed event) has happened.
        const pendingAt = list(node.trace.steps).find((/** @type {any} */ st) => st.time > node.at)?.time;
        for (const at of [...space.waits.map((/** @type {number} */ w) => node.at + w), ...(typeof pendingAt === 'number' ? [pendingAt] : [])]) {
          const k = key(node.trace, at);
          if (!seenKeys.has(k)) { seenKeys.add(k); next.push({ steps: node.steps, at, trace: node.trace }); }
        }
        for (const { event, payloads } of space.inputs) {
          for (const payload of payloads.slice(0, width)) {
            if (runs >= limit) break;
            const at = node.at + 1;
            const steps = [...node.steps, { at, event, payload }];
            runs++;
            const trace = runSteps(space.input, steps);
            if (!trace) continue;
            const got = exercisedItems(transitions, b.id, trace);
            if ([...got].some((it) => !by.has(it))) {
              candidates.push({ steps, covers: got });
              for (const it of got) if (!by.has(it)) by.set(it, '(generated)');
            }
            const k = key(trace, at);
            if (!seenKeys.has(k)) { seenKeys.add(k); next.push({ steps, at, trace }); }
          }
        }
      }
      if (runs >= limit) { stoppedBy = 'runs'; break; }
      frontier = next;
    }
    if (!open() || runs >= maxRuns) break;
  }
  return { runs, stoppedBy };
}

/**
 * The states of a machine its transitions can enter from the initial state, guards aside.
 * @param {Entity} b @param {Entity[]} transitions @returns {Set<string>}
 */
function enterable(b, transitions) {
  const reach = new Set([b.data.initial]);
  for (let grew = true; grew;) {
    grew = false;
    for (const t of transitions) if (reach.has(t.data.from) && !reach.has(t.data.to)) { reach.add(t.data.to); grew = true; }
  }
  return reach;
}

/**
 * @typedef {Object} MachineCoverage
 * @property {string} machine
 * @property {string[]} scenarios       the specification's scenarios that run it
 * @property {{id: string, error: string}[]} scenarioErrors
 * @property {{covered: number, total: number, byScenarios: number}} transitions
 * @property {{covered: number, total: number, byScenarios: number}} guards
 * @property {{item: string, kind: 'transition'|'guard', transition: string, outcome?: boolean, by: string|null}[]} items
 * @property {{name: string, steps: Step[], covers: string[], routes: any[]}[]} generated
 * @property {{bound: number, maxRuns: number, runs: number, complete: boolean, stoppedBy: 'states'|'bound'|'runs', inputs: string[], waits: number[]}} search
 */

/**
 * The coverage of every shipped implementation machine, the scenarios generated for what the specification's
 * scenarios leave out, and the findings.
 * @param {Model} model
 * @param {{bound?: number, maxRuns?: number, machines?: string[], search?: boolean}} [opts]
 * @returns {{machines: MachineCoverage[], findings: Diagnostic[]}}
 */
export function machineCoverage(model, opts = {}) {
  const bound = opts.bound ?? DEFAULT_BOUND;
  const maxRuns = opts.maxRuns ?? DEFAULT_MAX_RUNS;
  const severity = model.system.data.generation !== undefined ? 'error' : 'warning';
  /** @type {MachineCoverage[]} */
  const machines = [];
  /** @type {Diagnostic[]} */
  const findings = [];
  for (const b of shippedMachines(model)) {
    if (opts.machines && !opts.machines.includes(b.id)) continue;
    const { transitions, items } = machineItems(model, b);
    const scenarios = (model.byKind.scenario ?? []).filter((s) => list(s.data.behaviors).includes(b.id));
    /** @type {Map<string, string>} */
    const by = new Map();
    /** @type {{id: string, error: string}[]} */
    const scenarioErrors = [];
    for (const s of scenarios) {
      try {
        const trace = runEngine(engineInput(model, s.id));
        for (const it of exercisedItems(transitions, b.id, trace)) if (!by.has(it)) by.set(it, s.id);
        if (trace.outcome === 'error') scenarioErrors.push({ id: s.id, error: String(trace.steps.at(-1)?.error?.message ?? 'the run ended with an error') });
      } catch (e) {
        scenarioErrors.push({ id: s.id, error: /** @type {Error} */ (e).message });
      }
    }
    const byScenarios = new Set(by.keys());

    // The search, for what the scenarios leave out.
    /** @type {any} */
    let space;
    try {
      space = searchSpace(model, b, transitions, scenarios);
    } catch (e) {
      scenarioErrors.push({ id: `cover-${b.id}`, error: `the search cannot build an engine input: ${/** @type {Error} */ (e).message}` });
    }
    /** @type {{steps: Step[], covers: Set<string>}[]} */
    const candidates = [];
    const run = space && opts.search !== false ? search(b, transitions, items, space, by, candidates, bound, maxRuns) : { runs: 0, stoppedBy: /** @type {'states'|'bound'|'runs'} */ ('states') };
    const { runs, stoppedBy } = run;
    const complete = stoppedBy === 'states';

    // The generated scenarios: a greedy cover of what the scenarios leave out, shortest first on a tie.
    /** @type {{name: string, steps: Step[], covers: string[], routes: any[]}[]} */
    const generated = [];
    /** @type {Set<string>} */
    const want = new Set(items.filter((it) => !byScenarios.has(it) && by.has(it)));
    while (want.size) {
      let best = -1, bestGain = 0;
      candidates.forEach((c, i) => {
        const gain = [...c.covers].filter((it) => want.has(it)).length;
        if (gain > bestGain || (gain === bestGain && gain > 0 && c.steps.length < candidates[best].steps.length)) { best = i; bestGain = gain; }
      });
      if (best < 0) break;
      const c = candidates[best];
      const covers = items.filter((it) => want.has(it) && c.covers.has(it));
      const name = `cover-${b.id}-${generated.length + 1}`;
      generated.push({ name, steps: c.steps, covers, routes: space?.routes ?? [] });
      for (const it of covers) { want.delete(it); by.set(it, name); }
    }

    const itemRows = items.map((it) => {
      const [k, tid, outcome] = it.split(':');
      return { item: it, kind: /** @type {'transition'|'guard'} */ (k === 't' ? 'transition' : 'guard'), transition: tid, ...(k === 'g' ? { outcome: outcome === 'true' } : {}), by: by.get(it) ?? null };
    });
    const count = (/** @type {'transition'|'guard'} */ kind) => {
      const rows = itemRows.filter((r) => r.kind === kind);
      return { covered: rows.filter((r) => r.by !== null).length, total: rows.length, byScenarios: rows.filter((r) => byScenarios.has(r.item)).length };
    };
    machines.push({
      machine: b.id,
      scenarios: scenarios.map((s) => s.id),
      scenarioErrors,
      transitions: count('transition'),
      guards: count('guard'),
      items: itemRows,
      generated,
      search: { bound, maxRuns, runs, complete, stoppedBy, inputs: space ? space.inputs.map((/** @type {any} */ i) => i.event) : [], waits: space ? space.waits : [] },
    });

    const entered = enterable(b, transitions);
    for (const t of transitions) {
      if (by.has(`t:${t.id}`) || opts.search === false) continue;
      const how = !entered.has(t.data.from)
        ? `its source state "${t.data.from}" is entered by no transition from the initial state "${b.data.initial}", so no sequence of events reaches it`
        : stoppedBy === 'states'
          ? `the search reached every state it could (${runs} runs) without taking it, so no sequence of the offered events and payloads reaches it`
          : `no sequence of up to ${bound} input events and waits the search tried reaches it (${runs} runs, stopped by the ${stoppedBy === 'bound' ? `bound of ${bound} action${bound === 1 ? '' : 's'}` : `bound of ${maxRuns} runs`}); it is unreachable within that bound`;
      findings.push({
        code: 'machine.transition-unreachable', severity, entityId: t.id, loc: t.loc, path: t.path,
        message: `Transition "${t.id}" of shipped machine "${b.id}" (${t.data.from} -> ${t.data.to} on ${t.data.on}) is exercised by no scenario, and ${how}. The inputs offered were ${space?.inputs.length ? space.inputs.map((/** @type {any} */ i) => `"${i.event}"`).join(', ') : 'none'}.`,
      });
    }
  }
  return { machines, findings };
}

/**
 * The apply operations that add the generated scenarios to the specification (CreateEntity of kind scenario),
 * each tagged generated-coverage and saying what it covers.
 * @param {Model} model @param {MachineCoverage[]} machines @returns {any[]}
 */
export function coverageOperations(model, machines) {
  /** @type {any[]} */
  const ops = [];
  for (const m of machines) {
    const template = (model.byKind.scenario ?? []).find((s) => list(s.data.behaviors).includes(m.machine))?.data ?? {};
    for (const g of m.generated) {
      if (model.entities.has(g.name)) continue;
      // Only the routes for the events the scenario delivers.
      const events = new Set(g.steps.map((s) => s.event));
      const r = g.routes.filter((x) => events.has(x.event));
      const covers = g.covers.map((it) => {
        const [k, tid, outcome] = it.split(':');
        return k === 't' ? tid : `${tid} (guard ${outcome})`;
      });
      ops.push({
        type: 'CreateEntity',
        kind: 'scenario',
        data: {
          id: g.name,
          name: `Coverage of ${m.machine} ${g.name.slice(g.name.lastIndexOf('-') + 1)}`,
          description: `Generated by exegra cover-machines: exercises ${covers.join(', ')}.`,
          tags: [COVERAGE_TAG],
          behaviors: [m.machine],
          ...(typeof template.timeUnit === 'string' ? { timeUnit: template.timeUnit } : {}),
          ...(template.maxSteps !== undefined ? { maxSteps: template.maxSteps } : {}),
          ...(r.length ? { routes: r } : {}),
          steps: g.steps.map((s) => ({ at: s.at, event: s.event, ...(Object.keys(s.payload).length ? { payload: s.payload } : {}) })),
        },
      });
    }
  }
  return ops;
}
