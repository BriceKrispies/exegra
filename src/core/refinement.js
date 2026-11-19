// Refinement of a model machine by an implementation machine (docs/claims-and-evidence.md, "Refinement").
//
// An implementation behavior I declares `refines: A` and a mapping `refinement: {states, variables,
// transitions}`. The check is a forward simulation with that mapping, step by step over traces of I that
// the engine produced: the initial configuration of each I machine maps to A's initial configuration, and
// every transition I fires maps to the transition of A that A itself would fire from the mapped
// configuration on the same event, with equal mapped post-configuration and the same emitted events, or to
// a stutter (`null`) that changes nothing the mapping can see. Timers the implementation sets are compared
// with the model's timers when the model transition sets some, and are internal to the implementation
// otherwise; model expressions may read other behaviors from the same trace configuration.
//
// Pure: it reads a model and traces and evaluates expressions with src/core/expr.js. Running the
// scenarios is the caller's (src/core/claims.js).

import { parseExpr, evalExpr, ExprError } from './expr.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

/**
 * One step of I as the check saw it, in trace order. `model` is the model transition the mapping names
 * (null for a stutter); `ok` is false only on the failing step, which is always the last one listed.
 * @typedef {{scenario: string, stepIndex: number, machine: string, event: string|null, transition: string|null,
 *   implFrom: string, implTo: string, model: string|null, modelFrom: string|null, modelTo: string|null, ok: boolean}} RefinementStep
 * @typedef {{reason: string, summary: string, entities: string[], scenario: string, stepIndex: number, trace: RefinementStep[]}} RefinementFailure
 * @typedef {{checkedSteps: number, movingSteps: number, machines: string[], failure: RefinementFailure|null,
 *   unsupported: string|null}} RefinementOutcome
 */

/** Raised when a model expression reads something the mapping does not define. */
class Unsupported extends Error {}

/**
 * Structural equality of two engine values (JSON data): numbers, strings, booleans and null by `===`,
 * arrays element-wise, objects by their own keys regardless of order.
 * @param {any} a @param {any} b @returns {boolean}
 */
export function sameValue(a, b) {
  if (a === b) return true;
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false;
  if (Array.isArray(a) !== Array.isArray(b)) return false;
  if (Array.isArray(a)) return a.length === b.length && a.every((x, i) => sameValue(x, b[i]));
  const ka = Object.keys(a), kb = Object.keys(b);
  return ka.length === kb.length && ka.every((k) => Object.hasOwn(b, k) && sameValue(a[k], b[k]));
}

/** @param {any} v */
const show = (v) => (v === undefined ? 'nothing' : JSON.stringify(v));

/**
 * The parts of a refinement a check needs, read from the model. Null when I does not declare a usable one.
 * @param {Model} model @param {Entity} impl
 */
export function refinementOf(model, impl) {
  const target = typeof impl.data.refines === 'string' ? model.entities.get(impl.data.refines) : undefined;
  const map = impl.data.refinement;
  if (!target || target.kind !== 'behavior' || !map || typeof map !== 'object') return null;
  const obj = (/** @type {any} */ v) => (v && typeof v === 'object' && !Array.isArray(v) ? v : {});
  return {
    model: target,
    states: /** @type {Record<string, string>} */ (obj(map.states)),
    variables: /** @type {Record<string, string>} */ (obj(map.variables)),
    transitions: /** @type {Record<string, string|null>} */ (obj(map.transitions)),
    // Implementation time units per model tick (docs/claims-and-evidence.md, "Refinement"); 1 when absent.
    timeScale: typeof map.timeScale === 'number' && Number.isFinite(map.timeScale) && map.timeScale > 0 ? map.timeScale : 1,
  };
}

/** The declared variables of a behavior, in order. @param {Entity} b @returns {{name: string, initial: any}[]} */
function variablesOf(b) {
  return (Array.isArray(b.data.variables) ? b.data.variables : []).filter((/** @type {any} */ v) => v && typeof v.name === 'string');
}

/**
 * Check every step of the implementation behavior in one trace against its model.
 * @param {Model} model @param {Entity} impl @param {any} trace @param {string} scenario
 * @returns {RefinementOutcome}
 */
export function checkRefinementTrace(model, impl, trace, scenario) {
  const ref = refinementOf(model, impl);
  if (!ref) return { checkedSteps: 0, movingSteps: 0, machines: [], failure: null, unsupported: `Behavior "${impl.id}" declares no usable refinement.` };
  const A = ref.model;
  const aVars = variablesOf(A);
  const iVars = variablesOf(impl);
  /** @type {Map<string, any>} */
  const parsedMaps = new Map();
  for (const v of aVars) {
    const src = ref.variables[v.name];
    if (typeof src !== 'string') return { checkedSteps: 0, movingSteps: 0, machines: [], failure: null, unsupported: `The refinement of "${impl.id}" gives no expression for model variable "${v.name}".` };
    const p = parseExpr(src);
    if (!p.ok) return { checkedSteps: 0, movingSteps: 0, machines: [], failure: null, unsupported: `The mapping of "${v.name}" does not parse: ${p.error.message}.` };
    parsedMaps.set(v.name, p.ast);
  }
  const aTransitions = (model.byKind.transition ?? []).filter((t) => t.owner === A.id);
  /** @type {RefinementStep[]} */
  const seen = [];
  const machines = new Set();
  let checkedSteps = 0;
  let movingSteps = 0;

  /**
   * The key of a machine of `behaviorId` in a configuration. A format-2 trace names the instance of a fired
   * entry (`0` for a behavior without `instances`) while such a behavior's machine key is its bare id; a
   * counted or keyed instance is `<id>#<json of the instance>`. Null when the configuration has neither.
   * @param {any} config @param {string} behaviorId @param {any} instance
   */
  const keyIn = (config, behaviorId, instance) => {
    const ms = config?.machines ?? {};
    if (instance !== undefined) {
      const k = `${behaviorId}#${JSON.stringify(instance)}`;
      if (Object.hasOwn(ms, k)) return k;
    }
    return Object.hasOwn(ms, behaviorId) ? behaviorId : null;
  };
  const isImplKey = (/** @type {string} */ k) => k === impl.id || k.startsWith(`${impl.id}#`);
  /** I's own machine before it was created (a keyed instance): its declared initial configuration. */
  const fresh = () => ({ state: impl.data.initial, vars: Object.fromEntries(iVars.map((v) => [v.name, v.initial])) });

  /** Mapped model variables of an I machine. @param {{vars: Record<string, any>}} m */
  const mapVars = (m) => {
    /** @type {Record<string, any>} */
    const out = {};
    for (const v of aVars) {
      out[v.name] = evalExpr(parsedMaps.get(v.name), (path) => (path.length === 1 && m.vars && Object.hasOwn(m.vars, path[0]) ? m.vars[path[0]] : undefined));
    }
    return out;
  };

  /**
   * The entries a transition's `emitted` list holds, told apart by the transition's own effects: each `emit`
   * and each `timer` effect creates exactly one entry, in effect order (a `cancel` creates none). Null when the
   * effects cannot be matched to the entries (a fan-out, a link, a resource effect, or a count that differs).
   * `emits` are the emits, delayed or not, each tagged with its kind; `timers` the timers. A delayed emit goes to
   * its receivers and a timer back to its own machine, so neither ever stands in for the other.
   * @param {string} transitionId @param {any[]} emitted
   * @returns {{emits: any[], timers: any[]}|null}
   */
  const splitEmitted = (transitionId, emitted) => {
    const t = model.entities.get(transitionId);
    /** @type {{kind: 'emit'|'delayed-emit'|'timer', event: string}[]} */
    const kinds = [];
    for (const fx of Array.isArray(t?.data.effects) ? t.data.effects : []) {
      if (!fx || typeof fx !== 'object') continue;
      if ('timer' in fx) kinds.push({ kind: 'timer', event: fx.emit });
      else if ('emit' in fx) {
        if (fx.fanout === true || 'via' in fx) return null;
        kinds.push({ kind: isDelayed(fx) ? 'delayed-emit' : 'emit', event: fx.emit });
      } else if ('use' in fx || 'acquire' in fx || 'release' in fx) return null;
    }
    if (kinds.length !== emitted.length || kinds.some((k, i) => k.event !== emitted[i].event)) return null;
    const tagged = emitted.map((e, i) => ({ ...e, kind: kinds[i].kind }));
    return {
      emits: tagged.filter((e) => e.kind !== 'timer'),
      timers: tagged.filter((e) => e.kind === 'timer'),
    };
  };

  /**
   * @param {string} reason @param {string} summary @param {RefinementStep} step @param {string[]} entities
   * @returns {RefinementOutcome}
   */
  const fail = (reason, summary, step, entities) => {
    step.ok = false;
    seen.push(step);
    return {
      checkedSteps, movingSteps, machines: [...machines], unsupported: null,
      failure: { reason, summary, entities: [...new Set([impl.id, A.id, ...entities])], scenario, stepIndex: step.stepIndex, trace: seen.slice() },
    };
  };

  /**
   * The initial condition for one I machine. Null when it holds.
   * @param {string} key @param {{state: string, vars: Record<string, any>}} m @param {number} stepIndex
   */
  const checkInitial = (key, m, stepIndex) => {
    machines.add(key);
    const mapped = ref.states[m.state];
    const step = { scenario, stepIndex, machine: key, event: null, transition: null, implFrom: m.state, implTo: m.state, model: null, modelFrom: mapped ?? null, modelTo: mapped ?? null, ok: true };
    if (mapped !== A.data.initial) {
      return fail('initial-state', `The initial state "${m.state}" of ${key} maps to ${mapped === undefined ? 'no model state' : `"${mapped}"`}, but the initial state of "${A.id}" is "${A.data.initial}".`, step, [m.state, A.data.initial]);
    }
    let vars;
    try { vars = mapVars(m); } catch (e) {
      if (!(e instanceof ExprError)) throw e;
      return fail('mapping-error', `The variable mapping cannot be evaluated on the initial configuration of ${key}: ${e.message}.`, step, []);
    }
    for (const v of aVars) {
      if (!sameValue(vars[v.name], v.initial)) {
        return fail('initial-variables', `On the initial configuration of ${key}, model variable "${v.name}" maps to ${show(vars[v.name])}, but its initial value in "${A.id}" is ${show(v.initial)}.`, step, []);
      }
    }
    return null;
  };

  for (const [key, m] of Object.entries(trace.initial?.machines ?? {})) {
    if (!isImplKey(key)) continue;
    const r = checkInitial(key, /** @type {any} */ (m), -1);
    if (r) return r;
  }

  /**
   * Another behavior's state or variable, read by a model expression (`<behavior>.state`, `<behavior>.<var>`),
   * from a configuration of the run: the machine that ran under that id, or else the one machine of the run
   * whose behavior refines it, read through that behavior's refinement mapping. A behavior with several
   * instances, or one that nothing in the run stands for, is not resolved.
   * @param {any} config @param {string} behaviorId @param {string} name
   */
  const readOther = (config, behaviorId, name) => {
    const ms = config?.machines ?? {};
    const single = (/** @type {string} */ id) => {
      if (Object.hasOwn(ms, id)) return id;
      const keys = Object.keys(ms).filter((k) => k.startsWith(`${id}#`));
      if (keys.length > 1) throw new Unsupported(`it reads "${behaviorId}.${name}", but "${id}" has ${keys.length} instances in the run`);
      return keys[0] ?? null;
    };
    const direct = single(behaviorId);
    if (direct) {
      const m = ms[direct];
      if (name === 'state') return m.state;
      return m.vars && Object.hasOwn(m.vars, name) ? m.vars[name] : undefined;
    }
    const standIns = (model.byKind.behavior ?? []).filter((b) => b.data.refines === behaviorId && single(b.id));
    if (standIns.length !== 1) throw new Unsupported(`it reads "${behaviorId}.${name}", but ${standIns.length ? 'several machines of the run refine' : 'no machine of the run is or refines'} "${behaviorId}"`);
    const r = refinementOf(model, standIns[0]);
    const m = ms[/** @type {string} */ (single(standIns[0].id))];
    if (!r) throw new Unsupported(`it reads "${behaviorId}.${name}" through "${standIns[0].id}", which declares no usable refinement`);
    if (name === 'state') return r.states[m.state];
    const src = r.variables[name];
    if (typeof src !== 'string') throw new Unsupported(`it reads "${behaviorId}.${name}", which the refinement of "${standIns[0].id}" does not map`);
    return evalExpr(parseOrThrow(src), (path) => (path.length === 1 && m.vars && Object.hasOwn(m.vars, path[0]) ? m.vars[path[0]] : undefined));
  };

  let before = trace.initial;
  for (const step of trace.steps ?? []) {
    const fired = step.fired ?? [];
    for (let fi = 0; fi < fired.length; fi++) {
      const f = fired[fi];
      if (f.behavior !== impl.id) continue;
      const key = keyIn(before, impl.id, f.instance) ?? keyIn(step.config, impl.id, f.instance) ?? impl.id;
      const preKnown = before?.machines && Object.hasOwn(before.machines, key);
      const pre = preKnown ? before.machines[key] : fresh();
      if (!preKnown && !machines.has(key)) {
        const r = checkInitial(key, pre, step.index);
        if (r) return r;
      }
      const post = step.config?.machines?.[key];
      checkedSteps++;
      const target = Object.hasOwn(ref.transitions, f.transition) ? ref.transitions[f.transition] : undefined;
      const mFrom = ref.states[f.from] ?? null;
      const mTo = ref.states[f.to] ?? null;
      /** @type {RefinementStep} */
      const rs = { scenario, stepIndex: step.index, machine: key, event: step.event?.id ?? null, transition: f.transition, implFrom: f.from, implTo: f.to, model: target ?? null, modelFrom: mFrom, modelTo: mTo, ok: true };
      if (target === undefined) return fail('unmapped-transition', `Transition "${f.transition}" of "${impl.id}" fired, but the refinement does not map it.`, rs, [f.transition]);
      if (!post) return fail('missing-configuration', `The trace has no configuration of ${key} after step ${step.index}.`, rs, [f.transition]);
      let preVars, postVars;
      try { preVars = mapVars(pre); postVars = mapVars(post); } catch (e) {
        if (!(e instanceof ExprError)) throw e;
        return fail('mapping-error', `The variable mapping cannot be evaluated around step ${step.index}: ${e.message}.`, rs, [f.transition]);
      }
      const split = splitEmitted(f.transition, f.emitted ?? []);
      if (!split) return { checkedSteps, movingSteps, machines: [...machines], failure: null, unsupported: `At step ${step.index} of scenario "${scenario}", the events transition "${f.transition}" emitted cannot be told apart from its timers (a fan-out, a link or a resource effect).` };

      if (target === null) {
        if (mFrom !== mTo) return fail('stutter-state', `Transition "${f.transition}" is mapped to a stutter, but it moves from "${f.from}" (model "${mFrom}") to "${f.to}" (model "${mTo}").`, rs, [f.transition, f.from, f.to]);
        for (const v of aVars) {
          if (!sameValue(preVars[v.name], postVars[v.name])) return fail('stutter-variables', `Transition "${f.transition}" is mapped to a stutter, but it changes model variable "${v.name}" from ${show(preVars[v.name])} to ${show(postVars[v.name])}.`, rs, [f.transition]);
        }
        if (split.emits.length) return fail('stutter-emits', `Transition "${f.transition}" is mapped to a stutter, but it emits ${split.emits.map((/** @type {any} */ e) => `"${e.event}"`).join(', ')}; a stutter emits nothing.`, rs, [f.transition]);
        seen.push(rs);
        continue;
      }

      movingSteps++;
      const a = model.entities.get(target);
      if (!a || a.kind !== 'transition' || a.owner !== A.id) return fail('unknown-model-transition', `Transition "${f.transition}" is mapped to "${target}", which is not a transition of "${A.id}".`, rs, [f.transition]);
      rs.modelFrom = mFrom;
      if (a.data.from !== mFrom) return fail('model-from', `Transition "${f.transition}" leaves "${f.from}", which maps to "${mFrom}", but model transition "${a.id}" leaves "${a.data.from}".`, rs, [f.transition, a.id]);
      if (a.data.on !== rs.event) return fail('model-event', `Transition "${f.transition}" fired on "${rs.event}", but model transition "${a.id}" is triggered by "${a.data.on}".`, rs, [f.transition, a.id]);
      if (a.data.to !== mTo) return fail('model-to', `Transition "${f.transition}" enters "${f.to}", which maps to "${mTo}", but model transition "${a.id}" enters "${a.data.to}".`, rs, [f.transition, a.id]);
      if (a.data.faultOnly === true) return fail('model-fault-only', `Transition "${f.transition}" is mapped to "${a.id}", which exists in "${A.id}" only under a fault (faultOnly).`, rs, [f.transition, a.id]);

      const payload = step.event?.payload ?? {};
      // The model's clock: the trace time divided by the time scale (one IEEE double division).
      const modelTime = step.time / ref.timeScale;
      /**
       * Where another machine is read from: a guard reads the configuration before the step; an effect reads
       * it as the engine's effects do, after the step for a machine that fired earlier in this step (scenario
       * order) and before it otherwise.
       * @param {string} behaviorId
       */
      const effectConfig = (behaviorId) => {
        const at = fired.findIndex((e) => e.behavior === behaviorId || (model.entities.get(e.behavior)?.data.refines === behaviorId));
        return at >= 0 && at < fi ? step.config : before;
      };
      /** @param {Record<string, any>} vars @param {'guard'|'effect'} phase */
      const resolver = (vars, phase) => (/** @type {string[]} */ path) => {
        if (path.length === 1 && path[0] === 'time') return modelTime;
        if (path.length === 1 && Object.hasOwn(vars, path[0])) return vars[path[0]];
        if (path.length === 2 && path[0] === 'event') return Object.hasOwn(payload, path[1]) ? payload[path[1]] : undefined;
        if (path.length === 2 && path[0] === A.id) return path[1] === 'state' ? mFrom : Object.hasOwn(vars, path[1]) ? vars[path[1]] : undefined;
        if (path.length === 2) return readOther(phase === 'guard' ? before : effectConfig(path[0]), path[0], path[1]);
        throw new Unsupported(`it reads "${path.join('.')}", which the refinement check does not resolve (it resolves the model's own variables, event fields, time and two-part references to other behaviors)`);
      };
      /** Evaluate a guard of A on the mapped pre-variables. @param {Entity} t @returns {boolean} */
      const guardHolds = (t) => {
        const g = t.data.guard;
        if (typeof g !== 'string' || !g.trim()) return true;
        const v = evalExpr(parseOrThrow(g), resolver(preVars, 'guard'));
        if (typeof v !== 'boolean') throw new ExprError(`Guard "${g}" of transition "${t.id}" did not evaluate to a boolean.`);
        return v;
      };
      try {
        // A takes the first eligible transition in declaration order whose guard holds; that must be `a`.
        for (const t of aTransitions) {
          if (t.data.from !== mFrom || t.data.on !== rs.event || t.data.faultOnly === true) continue;
          if (t.id === a.id) break;
          if (guardHolds(t)) return fail('model-not-chosen', `Transition "${f.transition}" is mapped to "${a.id}", but from "${mFrom}" on "${rs.event}" the model would fire "${t.id}", declared earlier, whose guard holds.`, rs, [f.transition, a.id, t.id]);
        }
        if (!guardHolds(a)) return fail('model-guard-false', `Transition "${f.transition}" is mapped to "${a.id}", whose guard \`${a.data.guard}\` is false on the mapped variables ${JSON.stringify(preVars)} and the event payload ${JSON.stringify(payload)}.`, rs, [f.transition, a.id]);

        // A's effects, in order, on the mapped pre-variables: a later effect reads an earlier set.
        const vars = { ...preVars };
        const evalPayload = (/** @type {any} */ p) => {
          /** @type {Record<string, any>} */
          const out = {};
          for (const [k, v] of Object.entries(p && typeof p === 'object' ? p : {})) out[k] = typeof v === 'string' ? evalExpr(parseOrThrow(v), resolver(vars, 'effect')) : v;
          return out;
        };
        /** The model's emits, delayed or not, in effect order. @type {{kind: string, event: string, after: any, payload: Record<string, any>}[]} */
        const emits = [];
        /** @type {{kind: string, event: string, after: any, payload: Record<string, any>}[]} */
        const timers = [];
        for (const fx of Array.isArray(a.data.effects) ? a.data.effects : []) {
          if (!fx || typeof fx !== 'object') continue;
          if ('set' in fx) {
            if (fx.to && typeof fx.to === 'object') throw new Unsupported(`model transition "${a.id}" sets "${fx.set}" to a sampled value`);
            vars[fx.set] = typeof fx.to === 'string' ? evalExpr(parseOrThrow(fx.to), resolver(vars, 'effect')) : fx.to;
          } else if ('timer' in fx) {
            timers.push({ kind: 'timer', event: fx.emit, after: fx.after, payload: evalPayload(fx.payload) });
          } else if ('emit' in fx) {
            emits.push({ kind: isDelayed(fx) ? 'delayed-emit' : 'emit', event: fx.emit, after: fx.after, payload: evalPayload(fx.payload) });
          } else if ('cancel' in fx) {
            // Cancels are not compared (docs, "Refinement").
          } else {
            throw new Unsupported(`model transition "${a.id}" has a resource effect, which the refinement check does not model`);
          }
        }
        for (const v of aVars) {
          if (!sameValue(vars[v.name], postVars[v.name])) return fail('post-variables', `After transition "${f.transition}", model variable "${v.name}" maps to ${show(postVars[v.name])}, but model transition "${a.id}" makes it ${show(vars[v.name])}.`, rs, [f.transition, a.id]);
        }
        const ids = (/** @type {{event: string}[]} */ xs) => xs.map((e) => e.event).join(', ') || 'nothing';
        /** @param {'emits'|'timers'} reason @param {any[]} got @param {any[]} want @param {string} verb */
        const compare = (reason, got, want, verb) => {
          if (got.length !== want.length || want.some((e, i) => e.event !== got[i].event)) {
            return fail(reason, `Transition "${f.transition}" ${verb} ${ids(got)}, but model transition "${a.id}" ${verb} ${ids(want)}.`, rs, [f.transition, a.id]);
          }
          for (let i = 0; i < want.length; i++) {
            const p = got[i].payload ?? {};
            for (const [k, v] of Object.entries(want[i].payload)) {
              if (!Object.hasOwn(p, k) || !sameValue(p[k], v)) return fail(reason, `Transition "${f.transition}" ${verb} "${want[i].event}" with ${k} = ${show(p[k])}, but model transition "${a.id}" ${verb} it with ${k} = ${show(v)}.`, rs, [f.transition, a.id]);
            }
            // An emit is delayed exactly when the model's is; a timer is not an emit and was told apart above.
            if (reason === 'emits' && want[i].kind !== got[i].kind) {
              return want[i].kind === 'delayed-emit'
                ? fail(reason, `Transition "${f.transition}" emits "${want[i].event}" at once, but model transition "${a.id}" emits it after a delay.`, rs, [f.transition, a.id])
                : fail(reason, `Transition "${f.transition}" emits "${want[i].event}" after a delay, but model transition "${a.id}" emits it at once.`, rs, [f.transition, a.id]);
            }
            if (want[i].kind !== 'emit' && typeof want[i].after === 'number' && got[i].time !== step.time + want[i].after * ref.timeScale) {
              return fail(reason, `Transition "${f.transition}" ${verb} "${want[i].event}" for time ${got[i].time}, but model transition "${a.id}" ${verb} it ${want[i].after} ticks (${want[i].after * ref.timeScale} implementation units) after time ${step.time}.`, rs, [f.transition, a.id]);
            }
          }
          return null;
        };
        const e1 = compare('emits', split.emits, emits, 'emits');
        if (e1) return e1;
        // A timer is compared only when the model sets timers here; otherwise it is internal to the implementation.
        // A timer never realises a model emit, delayed or not: the emit list above already lacks it.
        if (timers.length) {
          const e2 = compare('timers', split.timers, timers, 'sets timers for');
          if (e2) return e2;
        }
      } catch (e) {
        if (e instanceof Unsupported) return { checkedSteps, movingSteps, machines: [...machines], failure: null, unsupported: `At step ${step.index} of scenario "${scenario}", ${e.message}.` };
        if (e instanceof ExprError) return fail('model-expression-error', `Evaluating model transition "${a.id}" on the mapped variables failed: ${e.message}.`, rs, [f.transition, a.id]);
        throw e;
      }
      seen.push(rs);
    }
    if (!step.error) before = step.config;
  }
  return { checkedSteps, movingSteps, machines: [...machines], failure: null, unsupported: null };
}

/** An emit effect whose event is delivered later: it has an `after` other than 0. @param {any} fx */
function isDelayed(fx) {
  return fx.after !== undefined && fx.after !== null && fx.after !== 0;
}

/** @param {string} src */
function parseOrThrow(src) {
  const p = parseExpr(src);
  if (!p.ok) throw new ExprError(p.error.message);
  return p.ast;
}
