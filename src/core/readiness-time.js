// Readiness rules for time and integers in implementation-level machines (WG-4902,
// docs/semantics.md, "Time" and "Numbers"). They keep a machine's meaning the same in the simulator,
// whose clock starts at 0, and in generated code, whose clock is the Unix epoch:
//
// - ready.time-difference: `time - X` is only read where `X <= time` (or `time >= X`) is
//   established by an earlier conjunct of an enclosing `&&` chain or the premise of a `=>`; a value set in
//   the future (clock skew between two processes) must not read as fresh. For an effect, the guard's
//   top-level conjuncts count.
// - ready.time-epoch: a variable compared with `time` (or subtracted from it, or it from `time`)
//   must hold a value derived from `time` wherever it is read: it is set from an expression reading `time`
//   on every path into the transition's state, or an earlier conjunct is a boolean variable that starts
//   false and is set true only by transitions that also set the variable from `time`. Otherwise the
//   variable can still hold its literal initial value, a time near the epoch.
// - ready.delay-unit: the scenarios that run the machine agree on one time unit (sim-input.js,
//   machineTimeUnit); every fixed delay of an `emit ... after` or a timer, a bare number in that unit or a
//   duration string, is a whole number of milliseconds, the unit of generated code's timers; and a machine
//   that reads `time` runs in milliseconds, since generated code's `time` counts milliseconds.
// - ready.number-bound: a number literal in an expression is at most 2^53 - 1; an initial value of an
//   integer variable, and a scenario payload value of an integer payload field of an event the machine
//   receives, is a whole number in its type's range (u64 and i64 limited to +-(2^53 - 1)).
// Pure: no DOM, no I/O.

import { parseExpr, exprRefs, INT_RANGES } from './expr.js';
import { evalTypeOf, machineTimeUnit, durationIn, UNIT_NS } from './sim-input.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./expr.js').Ast} Ast */
/** @typedef {(code: string, entity: Entity, message: string, sub?: (string|number)[]) => void} Report */

const COMPARE = new Set(['<', '<=', '>', '>=', '==', '!=']);
const SAFE = 9007199254740991;

/** Structural equality of two syntax trees (positions ignored). @param {Ast} a @param {Ast} b @returns {boolean} */
function sameAst(a, b) {
  if (a.t !== b.t) return false;
  if (a.t === 'lit') return a.v === /** @type {any} */ (b).v;
  if (a.t === 'ref') return a.path.join('.') === /** @type {any} */ (b).path.join('.');
  if (a.t === 'un') return a.op === /** @type {any} */ (b).op && sameAst(a.a, /** @type {any} */ (b).a);
  return a.op === /** @type {any} */ (b).op && sameAst(a.a, /** @type {any} */ (b).a) && sameAst(a.b, /** @type {any} */ (b).b);
}

/** @param {Ast} a */
const isTime = (a) => a.t === 'ref' && a.path.length === 1 && a.path[0] === 'time';

/** The conjuncts of an `&&` chain, left to right. @param {Ast} a @returns {Ast[]} */
function conjuncts(a) {
  return a.t === 'bin' && a.op === '&&' ? [...conjuncts(a.a), ...conjuncts(a.b)] : [a];
}

/**
 * What a conjunct establishes for the conjuncts after it: `X <= time` / `time >= X` gives X (as a tree), a
 * bare variable `f` gives the flag f.
 * @param {Ast} c @returns {{bound?: Ast, flag?: string}}
 */
function established(c) {
  if (c.t === 'bin' && c.op === '<=' && isTime(c.b)) return { bound: c.a };
  if (c.t === 'bin' && c.op === '>=' && isTime(c.a)) return { bound: c.b };
  if (c.t === 'ref' && c.path.length === 1) return { flag: c.path[0] };
  return {};
}

/**
 * Walk an expression with the facts established around each node.
 * @param {Ast} a
 * @param {{bounds: Ast[], flags: Set<string>}} facts
 * @param {(node: Ast, facts: {bounds: Ast[], flags: Set<string>}) => void} visit
 */
function walk(a, facts, visit) {
  visit(a, facts);
  if (a.t === 'bin' && a.op === '&&') {
    let f = { bounds: [...facts.bounds], flags: new Set(facts.flags) };
    for (const c of conjuncts(a)) {
      walkInner(c, f, visit);
      const e = established(c);
      f = { bounds: e.bound ? [...f.bounds, e.bound] : f.bounds, flags: e.flag ? new Set([...f.flags, e.flag]) : f.flags };
    }
  } else if (a.t === 'bin' && a.op === '=>') {
    walk(a.a, facts, visit);
    let f = facts;
    for (const c of conjuncts(a.a)) {
      const e = established(c);
      f = { bounds: e.bound ? [...f.bounds, e.bound] : f.bounds, flags: e.flag ? new Set([...f.flags, e.flag]) : f.flags };
    }
    walk(a.b, f, visit);
  } else if (a.t === 'bin') { walk(a.a, facts, visit); walk(a.b, facts, visit); } else if (a.t === 'un') walk(a.a, facts, visit);
}

/** A conjunct of a chain: visited by `walk` itself, but its own `&&` is not split again. @param {Ast} c @param {any} f @param {any} visit */
function walkInner(c, f, visit) {
  if (c.t === 'bin' && c.op === '&&') walk(c, f, visit);
  else walk(c, f, visit);
}

/** The single-name references of a tree. @param {Ast} a */
const names = (a) => exprRefs(a).filter((p) => p.length === 1).map((p) => p[0]);

/**
 * The machine variables a node compares with `time`: a comparison, `-` or `+` with `time` on one side and
 * the variable on the other.
 * @param {Ast} n @param {Set<string>} vars @returns {string[]}
 */
function timeUses(n, vars) {
  if (n.t !== 'bin' || !(COMPARE.has(n.op) || n.op === '-' || n.op === '+')) return [];
  const l = names(n.a);
  const r = names(n.b);
  const pick = (/** @type {string[]} */ side) => side.filter((x) => x !== 'time' && vars.has(x));
  if (l.includes('time')) return pick(r);
  if (r.includes('time')) return pick(l);
  return [];
}

/**
 * The time and integer readiness rules of one implementation-level machine.
 * @param {Model} model @param {Entity} b @param {Entity[]} states @param {Entity[]} transitions @param {Report} report
 */
export function timeReadiness(model, b, states, transitions, report) {
  const list = (/** @type {any} */ v) => (Array.isArray(v) ? v : []);
  const variables = list(b.data.variables).filter((v) => v && typeof v.name === 'string');
  const vars = new Set(variables.map((v) => v.name));
  /** @param {any} src */
  const parse = (src) => {
    if (typeof src !== 'string') return null;
    const p = parseExpr(src);
    return p.ok ? p.ast : null;
  };

  // Time unit and delays.
  const tu = machineTimeUnit(model, b.id);
  if (tu.units.length > 1) {
    report('ready.delay-unit', b, `The scenarios running "${b.id}" use different time units (${tu.units.join(', ')}; ${tu.scenarios.join(', ')}); its bare-number delays and its reads of time need one unit.`);
  } else {
    const readsTime = transitions.some((t) => [t.data.guard, ...list(t.data.effects).flatMap((/** @type {any} */ fx) => (fx && typeof fx === 'object' ? [fx.to, fx.after?.expr, ...Object.values(fx.payload ?? {})] : []))]
      .some((src) => { const a = parse(src); return !!a && exprRefs(a).some((p) => p.length === 1 && p[0] === 'time'); }));
    if (readsTime && tu.unit !== 'ms') {
      report('ready.delay-unit', b, `"${b.id}" reads time, but its scenarios count time in ${tu.unit}; generated code's time counts milliseconds. Run it in scenarios with "timeUnit": "ms".`);
    }
    const unitNs = /** @type {Record<string, number>} */ (UNIT_NS)[tu.unit];
    for (const t of transitions) {
      list(t.data.effects).forEach((/** @type {any} */ fx, /** @type {number} */ i) => {
        if (!fx || typeof fx !== 'object' || !('after' in fx) || !('emit' in fx)) return;
        const d = fx.after && typeof fx.after === 'object' && 'expr' in fx.after ? fx.after.simulate : fx.after;
        if (typeof d !== 'number' && typeof d !== 'string') return;
        let ns;
        try { ns = typeof d === 'number' ? (unitNs === undefined ? NaN : d * unitNs) : durationIn(d, 'ns', `${t.id}.effects[${i}].after`); } catch { return; }
        if (!Number.isInteger(ns / 1000000)) {
          report('ready.delay-unit', t, `The delay ${JSON.stringify(d)}${typeof d === 'number' ? ` ${tu.unit}` : ''} of effect ${i} is not a whole number of milliseconds, the unit of generated code's timers.`, ['effects', i, 'after']);
        }
      });
    }
  }

  // Integer initial values.
  variables.forEach((v, i) => {
    const t = evalTypeOf(model, v.repr);
    if (t === undefined || !Object.hasOwn(INT_RANGES, t) || v.initial === undefined) return;
    const [lo, hi] = INT_RANGES[t];
    if (typeof v.initial !== 'number' || !Number.isInteger(v.initial) || v.initial < lo || v.initial > hi) {
      report('ready.number-bound', b, `The initial value ${JSON.stringify(v.initial)} of variable "${v.name}" is not a ${t} (a whole number in ${lo}..${hi}).`, ['variables', i, 'initial']);
    }
  });

  // Which variables a transition's effects set from `time` (directly or from a variable already set so),
  // and which they set otherwise.
  /** @param {Entity} t @param {Set<string>} inSet */
  const transfer = (t, inSet) => {
    const out = new Set(inSet);
    for (const fx of list(t.data.effects)) {
      if (!fx || typeof fx !== 'object' || typeof fx.set !== 'string') continue;
      const a = parse(fx.to);
      const reads = a ? names(a) : [];
      if (reads.includes('time') || reads.some((x) => out.has(x) && x !== fx.set)) out.add(fx.set);
      else out.delete(fx.set);
    }
    return out;
  };
  // Must-analysis over the state graph: the variables set from `time` on every path into each state.
  const all = new Set(vars);
  /** @type {Map<string, Set<string>>} */
  const atState = new Map(states.map((s) => [s.id, s.id === b.data.initial ? new Set() : new Set(all)]));
  for (let round = 0, changed = true; changed && round < 1000; round++) {
    changed = false;
    for (const s of states) {
      if (s.id === b.data.initial) continue;
      const incoming = transitions.filter((t) => t.data.to === s.id && atState.has(t.data.from));
      /** @type {Set<string>} */
      let meet = incoming.length ? new Set(all) : new Set();
      for (const t of incoming) {
        const o = transfer(t, /** @type {Set<string>} */ (atState.get(t.data.from)));
        meet = new Set([...meet].filter((x) => o.has(x)));
      }
      const cur = /** @type {Set<string>} */ (atState.get(s.id));
      if (meet.size !== cur.size || [...meet].some((x) => !cur.has(x))) { atState.set(s.id, meet); changed = true; }
    }
    // The initial state is also entered by transitions into it.
    const init = b.data.initial;
    const back = transitions.filter((t) => t.data.to === init && atState.has(t.data.from));
    if (back.length) {
      const cur = /** @type {Set<string>} */ (atState.get(init));
      if (cur && cur.size) {
        let meet = new Set(cur);
        for (const t of back) { const o = transfer(t, /** @type {Set<string>} */ (atState.get(t.data.from))); meet = new Set([...meet].filter((x) => o.has(x))); }
        if (meet.size !== cur.size) { atState.set(init, meet); changed = true; }
      }
    }
  }

  // Flags that witness a variable: start false, and every effect setting them to anything but false is in a
  // transition that also sets the variable from `time`.
  /** @param {string} flag @param {string} v */
  const witnesses = (flag, v) => {
    const fv = variables.find((x) => x.name === flag);
    if (!fv || fv.initial !== false) return false;
    for (const t of transitions) {
      const fxs = list(t.data.effects).filter((fx) => fx && typeof fx === 'object' && typeof fx.set === 'string');
      const setsFlag = fxs.some((fx) => fx.set === flag && fx.to !== false);
      if (!setsFlag) continue;
      if (!transfer(t, new Set()).has(v)) return false;
    }
    // The variable is never set from anything but `time` while the flag holds.
    for (const t of transitions) {
      for (const fx of list(t.data.effects)) {
        if (!fx || typeof fx !== 'object' || fx.set !== v) continue;
        const a = parse(fx.to);
        if (!a || !names(a).includes('time')) return false;
      }
    }
    return true;
  };

  for (const t of transitions) {
    const guard = parse(t.data.guard);
    const inSet = atState.get(t.data.from) ?? new Set();
    const top = { bounds: /** @type {Ast[]} */ ([]), flags: /** @type {Set<string>} */ (new Set()) };
    if (guard) for (const c of conjuncts(guard)) {
      const e = established(c);
      if (e.bound) top.bounds.push(e.bound);
      if (e.flag) top.flags.add(e.flag);
    }
    /** @type {Set<string>} */
    const reported = new Set();
    /** @param {Ast} a @param {string} src @param {(string|number)[]} sub @param {{bounds: Ast[], flags: Set<string>}} start */
    const check = (a, src, sub, start) => {
      walk(a, start, (n, facts) => {
        if (n.t === 'lit' && typeof n.v === 'number' && n.v > SAFE) {
          report('ready.number-bound', t, `Expression "${src}" has the literal ${n.v}, beyond 2^53 - 1 (9007199254740991), the largest integer every engine and target holds exactly.`, sub);
        }
        if (n.t === 'bin' && n.op === '-' && isTime(n.a) && !facts.bounds.some((x) => sameAst(x, n.b))) {
          report('ready.time-difference', t, `Expression "${src}" reads time - ${n.b.t === 'ref' ? n.b.path.join('.') : '(…)'} without first establishing that it is not in the future: write "X <= time && time - X ..." so a value set ahead of this clock (clock skew) is not read as recent.`, sub);
        }
        for (const v of timeUses(n, vars)) {
          if (inSet.has(v) || reported.has(v)) continue;
          if ([...facts.flags].some((f) => witnesses(f, v))) continue;
          reported.add(v);
          report('ready.time-epoch', t, `Expression "${src}" compares time with variable "${v}", which can still hold its initial value here (it is not set from time on every path into state "${t.data.from}"): the outcome would depend on where the clock starts (0 in the simulator, the Unix epoch in generated code). Set it from time first, or guard the read with a boolean variable that starts false and is set true only together with it.`, sub);
        }
      });
    };
    if (guard) check(guard, t.data.guard, ['guard'], { bounds: [], flags: new Set() });
    list(t.data.effects).forEach((/** @type {any} */ fx, /** @type {number} */ i) => {
      if (!fx || typeof fx !== 'object') return;
      const sub = ['effects', i];
      /** @param {any} src @param {(string|number)[]} at */
      const one = (src, at) => { const a = parse(src); if (a) check(a, src, at, top); };
      if ('set' in fx) one(fx.to, [...sub, 'to']);
      if (fx.payload && typeof fx.payload === 'object') for (const [k, v] of Object.entries(fx.payload)) one(v, [...sub, 'payload', k]);
      if (fx.after && typeof fx.after === 'object') one(fx.after.expr, [...sub, 'after', 'expr']);
    });
  }
}

/**
 * Scenario payload values of integer payload fields, for the events implementation-level machines receive.
 * @param {Model} model @param {Set<string>} received the event ids implementation-level machines receive
 * @param {Report} report
 */
export function scenarioIntegerReadiness(model, received, report) {
  const list = (/** @type {any} */ v) => (Array.isArray(v) ? v : []);
  for (const s of model.byKind.scenario ?? []) {
    list(s.data.steps).forEach((/** @type {any} */ st, /** @type {number} */ i) => {
      if (!st || !received.has(st.event) || !st.payload || typeof st.payload !== 'object') return;
      const ev = model.entities.get(st.event);
      for (const f of list(ev?.data?.payload)) {
        if (!f || !Object.hasOwn(st.payload, f.name)) continue;
        const t = evalTypeOf(model, f.type);
        if (t === undefined || !Object.hasOwn(INT_RANGES, t)) continue;
        const [lo, hi] = INT_RANGES[t];
        const x = st.payload[f.name];
        if (typeof x !== 'number' || !Number.isInteger(x) || x < lo || x > hi) {
          report('ready.number-bound', s, `Step ${i} gives ${f.name} = ${JSON.stringify(x)}, which is not a ${t} (a whole number in ${lo}..${hi}).`, ['steps', i, 'payload', f.name]);
        }
      }
    });
  }
}
