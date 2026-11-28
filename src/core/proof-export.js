// Proof export: a scenario's engine input and its state-invariant claims as a Lean file whose
// theorems the verified explorer of the behaviour calculus discharges (formal/Exegra/ProveB.lean over
// formal/Exegra/Core/BehavCheck.lean).
// Pure and deterministic: this module builds the exploration request, the Lean text and the
// per-claim results; tools/prove.js runs Lean. See docs/simulation.md, "Exhaustive exploration".

import { simulationInput } from './sim-input.js';
import { parseExpr, evalExpr, exprRefs, ExprError } from './expr.js';
import { requestLog } from './contract-trace.js';
import { scenarioMachineIds } from './pools.js';

/** @typedef {import('./types.js').Model} Model */

export const PROOF_METHOD = 'lean-exhaustive';
/** Default budget of distinct states one claim's search may visit. */
export const DEFAULT_MAX_STATES = 200000;
const TRACE_METHODS = ['state-invariant', 'precedes', 'eventually', 'never'];

// Claim expressions are read exactly as the trace check reads them (configResolver and the
// applicability rule of src/core/claims.js; the Lean side is claimResolveB in formal/Exegra/ProveB.lean):
// `time`, `<behavior>.state` and `<behavior>.<variable>`, every behavior one the scenario runs.

/** @param {any} config */
function configResolver(config) {
  return (/** @type {string[]} */ p) => {
    if (p.length === 1) return p[0] === 'time' ? config.time : undefined;
    if (p.length !== 2) return undefined;
    if (!config.machines || !Object.hasOwn(config.machines, p[0])) return undefined;
    const m = config.machines[p[0]];
    if (p[1] === 'state') return m.state;
    return m.vars && Object.hasOwn(m.vars, p[1]) ? m.vars[p[1]] : undefined;
  };
}

/** "a = 1, b = true": the values the references of an expression have. @param {any} ast @param {any} config */
function valuesText(ast, config) {
  const resolve = configResolver(config);
  const seen = new Set();
  const parts = [];
  for (const p of exprRefs(ast)) {
    const key = p.join('.');
    if (seen.has(key)) continue;
    seen.add(key);
    const v = resolve(p);
    parts.push(`${key} = ${v === undefined ? 'unknown' : JSON.stringify(v)}`);
  }
  return parts.join(', ');
}

/**
 * Can a temporal claim be checked in this scenario? As `applicable` of src/core/claims.js: its
 * transitions belong to behaviors the scenario runs and its expression refers only to those.
 * @param {Model} model @param {any} ev @param {Set<string>} behaviors
 */
function temporalApplicable(model, ev, behaviors) {
  /** @param {any} m */
  const matcherOk = (m) => {
    if (!m || typeof m !== 'object') return false;
    if (typeof m.event === 'string') return true;
    const t = typeof m.transition === 'string' ? model.entities.get(m.transition) : undefined;
    return !!t && t.kind === 'transition' && behaviors.has(/** @type {string} */ (t.owner));
  };
  switch (ev.method) {
    case 'precedes': return matcherOk(ev.first) && matcherOk(ev.then);
    case 'never': return matcherOk(ev.occurs);
    case 'eventually':
      return (ev.occurs !== undefined || ev.expr !== undefined) && (ev.occurs === undefined || matcherOk(ev.occurs)) && (ev.expr === undefined || applicable(ev.expr, behaviors));
  }
  return false;
}

/** Does the expression parse and refer only to `time` and behaviors of the scenario? @param {unknown} src @param {Set<string>} behaviors */
function applicable(src, behaviors) {
  if (typeof src !== 'string') return false;
  const p = parseExpr(src);
  return p.ok && exprRefs(p.ast).every((r) => (r.length === 1 ? r[0] === 'time' : behaviors.has(r[0])));
}

/**
 * The number of steps a run of the scenario may take: `stepBound` of the semantics,
 * `max 1 ⌈stepLimit⌉`.
 * @param {number} stepLimit
 */
export function stepBound(stepLimit) {
  return stepLimit <= 1 ? 1 : Math.max(1, Math.ceil(stepLimit));
}

/**
 * What `exegra prove` checks for a scenario: its engine input (exactly as simulate builds it),
 * the state-invariant claims that list it and apply to it, and the claims it cannot check.
 * @param {Model} model
 * @param {string} scenarioId
 * @param {{bound?: number, maxStates?: number}} [opts]
 */
export function proofPlan(model, scenarioId, opts = {}) {
  const input = simulationInput(model, scenarioId);
  const limit = stepBound(input.scenario.stepLimit);
  const requested = opts.bound;
  const bound = requested === undefined ? limit : Math.min(requested, limit);
  const scenario = model.entities.get(scenarioId);
  const behaviors = scenarioMachineIds(model, scenario);
  /** @type {{claimId: string, expr: string, temporal?: any}[]} */
  const claims = [];
  /** @type {{claimId: string, method: string, result: 'not-supported'|'not-evaluable', explanation: string}[]} */
  const skipped = [];
  for (const claim of model.byKind.claim ?? []) {
    if (claim.data.kind !== 'invariant' && claim.data.kind !== 'temporal') continue;
    const ev = claim.data.evaluate;
    if (!ev || typeof ev !== 'object' || !TRACE_METHODS.includes(ev.method)) continue;
    if (!Array.isArray(ev.scenarios) || !ev.scenarios.includes(scenarioId)) continue;
    if (ev.method !== 'state-invariant') {
      if (temporalApplicable(model, ev, behaviors)) {
        const { method, occurs, first, then, expr } = ev;
        claims.push({ claimId: claim.id, expr: expr ?? '', temporal: { method, ...(occurs !== undefined ? { occurs } : {}), ...(first !== undefined ? { first } : {}), ...(then !== undefined ? { then } : {}), ...(expr !== undefined ? { expr } : {}) } });
      } else {
        skipped.push({ claimId: claim.id, method: PROOF_METHOD, result: 'not-evaluable', explanation: `The "${ev.method}" claim names an occurrence or an expression that does not belong to this scenario's behaviors (or does not parse), so it was not explored.` });
      }
    } else if (!applicable(ev.expr, behaviors)) {
      const parsed = parseExpr(ev.expr);
      skipped.push({ claimId: claim.id, method: PROOF_METHOD, result: 'not-evaluable', explanation: parsed.ok ? 'The expression refers to a behavior the scenario does not run.' : `The expression does not parse: ${parsed.error.message}` });
    } else {
      claims.push({ claimId: claim.id, expr: ev.expr });
    }
  }
  return {
    scenarioId,
    input,
    inputText: JSON.stringify(input),
    stepLimit: input.scenario.stepLimit,
    bound,
    boundCapped: requested !== undefined && requested > limit,
    maxStates: opts.maxStates ?? DEFAULT_MAX_STATES,
    faults: input.scenario.faults,
    claims,
    skipped,
  };
}

/** @typedef {ReturnType<typeof proofPlan>} ProofPlan */

/** The request `exegra-lean explore` reads. @param {ProofPlan} plan */
export function exploreRequest(plan) {
  return JSON.stringify({
    input: plan.input,
    claims: plan.claims.filter((c) => !c.temporal).map((c) => ({ id: c.claimId, expr: c.expr })),
    bound: plan.bound,
    maxStates: plan.maxStates,
  });
}

/**
 * The request `exegra-lean temporal` reads. Its bound is one more than the step limit: the search
 * needs a last layer to find that the runs of the limit's length have no successor, and only
 * then may it report `holds` (a path cut off by the bound is `incomplete`).
 * @param {ProofPlan} plan
 */
export function temporalRequest(plan) {
  return JSON.stringify({
    input: plan.input,
    claims: plan.claims.filter((c) => c.temporal).map((c) => ({ id: c.claimId, evaluate: c.temporal })),
    bound: plan.bound + 1,
    maxStates: plan.maxStates,
  });
}

/** The Lean term of a matcher. @param {any} m */
function leanMatcher(m) {
  return typeof m.event === 'string' ? `(V2.ProveB.Matcher.event ${leanString(m.event)})` : `(V2.ProveB.Matcher.transition ${leanString(m.transition)})`;
}

/** The Lean term of a temporal form. @param {any} ev */
export function leanForm(ev) {
  if (ev.method === 'never') return `(V2.ProveB.Form.never ${leanMatcher(ev.occurs)})`;
  if (ev.method === 'precedes') return `(V2.ProveB.Form.precedes ${leanMatcher(ev.first)} ${leanMatcher(ev.then)})`;
  return `(V2.ProveB.Form.eventually ${ev.occurs === undefined ? 'none' : `(some ${leanMatcher(ev.occurs)})`} ${ev.expr === undefined ? 'none' : `(some ${leanString(ev.expr)})`})`;
}

/** A Lean string literal. @param {string} s */
export function leanString(s) {
  let out = '"';
  for (const ch of s) {
    const code = ch.codePointAt(0) ?? 0;
    if (ch === '"') out += '\\"';
    else if (ch === '\\') out += '\\\\';
    else if (ch === '\n') out += '\\n';
    else if (ch === '\r') out += '\\r';
    else if (ch === '\t') out += '\\t';
    else if (code < 0x20 || code === 0x7f) out += `\\x${code.toString(16).padStart(2, '0')}`;
    else out += ch;
  }
  return `${out}"`;
}

/** The theorem name of a claim: its id as a Lean identifier. @param {string} claimId */
export const theoremName = (claimId) => `«${claimId.replace(/[«»]/g, '')}»`;

/** The Lean namespace of a scenario's proof file. @param {string} scenarioId */
export const proofNamespace = (scenarioId) => `Prove.«${scenarioId.replace(/[«»]/g, '')}»`;

/** The file a scenario's proof is written to, relative to formal/. @param {string} scenarioId */
export const proofFileName = (scenarioId) => `generated/${scenarioId.replace(/[^A-Za-z0-9_-]/g, '_')}.lean`;

/**
 * The right-hand side of a claim's theorem: the result the explorer returned.
 * @param {any} r a result of `exegra-lean explore`
 */
function resultTerm(r) {
  if (r.verdict === 'counterexample') return `("counterexample", [${r.picks.join(', ')}])`;
  return `("${r.verdict}", [${r.states}])`;
}

/**
 * The Lean proof file: the engine input text, and per claim a theorem stating the result of the
 * calculus explorer on that text, discharged by evaluation.
 * @param {ProofPlan} plan
 * @param {{results: any[]}} explored the answer of `exegra-lean explore` and `temporal`
 */
export function leanProofFile(plan, explored) {
  const ns = proofNamespace(plan.scenarioId);
  const lines = [
    `-- Generated by \`exegra prove ${plan.scenarioId}\`. Do not edit; it is rewritten on every run.`,
    '-- Each theorem states the result of the explorer of the behaviour calculus (formal/Exegra/ProveB.lean)',
    '-- on this engine input for one claim; verdictOf_holds and tcheckB_holds give its meaning.',
    '-- The results are established by evaluation (native_decide).',
    'import Exegra.ProveB',
    '',
    'open Exegra',
    '',
    `namespace ${ns}`,
    '',
    '/-- The engine input, exactly as `exegra simulate` builds it. -/',
    `def inputText : String := ${leanString(plan.inputText)}`,
    `def bound : Nat := ${plan.bound}`,
    `def maxStates : Nat := ${plan.maxStates}`,
    '',
  ];
  plan.claims.forEach((c, i) => {
    const r = explored.results[i];
    if (c.temporal) {
      lines.push(`/-- Temporal claim \`${c.claimId}\` (${c.temporal.method}); tcheckB_holds and tcheckB_cex give the meaning of its result. -/`);
      lines.push(`theorem ${theoremName(c.claimId)} : V2.ProveB.tverdictOf inputText ${leanForm(c.temporal)} ${plan.bound + 1} maxStates = ${resultTerm(r)} := by native_decide`);
      lines.push('');
      return;
    }
    lines.push(`/-- Claim \`${c.claimId}\`: \`${c.expr.replace(/-\//g, '- /')}\`. -/`);
    lines.push(`theorem ${theoremName(c.claimId)} : V2.ProveB.verdictOf inputText ${leanString(c.expr)} bound maxStates = ${resultTerm(r)} := by native_decide`);
    lines.push('');
  });
  for (const c of plan.claims) lines.push(`#print axioms ${theoremName(c.claimId)}`);
  lines.push('', `end ${ns}`, '');
  return lines.join('\n');
}

/**
 * The axioms `#print axioms` reported, by theorem name (the last component, without guillemets).
 * @param {string} output
 * @returns {Map<string, string[]>}
 */
export function parseAxioms(output) {
  /** @type {Map<string, string[]>} */
  const out = new Map();
  const re = /'([^']+)' depends on axioms: \[([^\]]*)\]/g;
  for (const m of output.matchAll(re)) {
    const name = m[1].split('.').pop()?.replace(/[«»]/g, '') ?? m[1];
    out.set(name, m[2].split(',').map((s) => s.trim()).filter(Boolean));
  }
  const none = /'([^']+)' does not depend on any axioms/g;
  for (const m of output.matchAll(none)) out.set(m[1].split('.').pop()?.replace(/[«»]/g, '') ?? m[1], []);
  return out;
}

const STANDARD_AXIOMS = new Set(['propext', 'Classical.choice', 'Quot.sound']);

/** @param {string[]} axioms */
function trustText(axioms) {
  const extra = axioms.filter((a) => !STANDARD_AXIOMS.has(a));
  const evaluation = extra.length
    ? `the result was established by native_decide, which adds ${extra.map((a) => `\`${a}\``).join(', ')}: one axiom per statement, asserting that the compiled code evaluated it to true (the claim's \`verdictOf … = result\`), so the Lean compiler, the C compiler it uses and the Lean runtime are trusted`
    : 'the result was established by the kernel alone';
  return `The Lean kernel and Lean's standard axioms; ${evaluation}. The meaning of the result is proved with standard axioms only (verdictOf_holds, explore_holds_invariant, explore_cex_real, tcheckB_holds, tcheckB_cex); the theorem is about the engine input text the file embeds.`;
}

/**
 * A counterexample as simulate shows a run: its steps, a step list, and the request-log lines of
 * its contract events.
 * @param {Model} model @param {ProofPlan} plan @param {any} r @param {string} expr @param {boolean} withSteps
 */
export function renderCounterexample(model, plan, r, expr, withSteps) {
  /** @type {any[]} */
  const steps = r.steps;
  const last = steps.length ? steps[steps.length - 1].config : r.initial;
  const parsed = parseExpr(expr);
  let why = '';
  const failed = steps.length ? steps[steps.length - 1].error : undefined;
  if (failed) {
    // The run ends in the error state: a failed step violates every invariant (formal/Exegra/ProveB.lean).
    why = `The run fails in step ${steps.length - 1}: ${failed.message}. It ends in the error state, which no invariant allows.`;
  } else if (expr !== '' && parsed.ok) {
    try {
      const v = evalExpr(parsed.ast, configResolver(last));
      why = v === false ? `Invariant \`${expr}\` is false` : `Invariant \`${expr}\` evaluates to ${JSON.stringify(v)}, not true,`;
    } catch (e) {
      if (!(e instanceof ExprError)) throw e;
      why = `Invariant \`${expr}\` cannot be evaluated (${e.message})`;
    }
    why += ` ${steps.length ? `after step ${steps.length - 1}` : 'in the initial configuration'}: ${valuesText(parsed.ast, last)}.`;
  }
  /** @type {number[]} */
  const positions = r.positions ?? r.picks;
  const stepList = steps.map((s, i) => {
    const pick = positions[i];
    const order = pick > 0 ? ` [delivered ahead of ${pick} earlier simultaneous ${pick === 1 ? 'entry' : 'entries'}]` : '';
    const fired = s.fired.length ? ` → ${s.fired.map((/** @type {any} */ f) => `${f.behavior}: ${f.transition}`).join(', ')}` : '';
    const faults = s.faults.length ? ` (${s.faults.map((/** @type {any} */ f) => `${f.fault} ${f.effect}`).join(', ')})` : '';
    return `#${s.index} t=${s.time} ${s.kind} ${s.event.id}${order}${fired}${faults}`;
  });
  const trace = { scenarioId: plan.scenarioId, faults: r.faults, initial: r.initial, steps, outcome: 'running', final: last };
  const log = requestLog(model, /** @type {any} */ (trace)).map((e) => `#${e.step} t=${e.time} ${e.text}`);
  /** @type {Record<string, any>} */
  const out = {
    faults: r.faults,
    faultChoice: plan.faults.length ? `Active faults: ${r.faults.length ? r.faults.join(', ') : 'none'} (of ${plan.faults.join(', ')}).` : 'The scenario declares no faults.',
    choices: positions,
    stepCount: steps.length,
    explanation: why,
    stepList,
  };
  if (log.length) out.requestLog = log;
  if (withSteps) {
    out.initial = r.initial;
    out.steps = steps;
  }
  return out;
}

/** Does a step have the occurrence? @param {any} m @param {any} step */
function stepHas(m, step) {
  return m.event !== undefined ? step.kind === 'deliver' && step.event.id === m.event : Array.isArray(step.fired) && step.fired.some((/** @type {any} */ f) => f.transition === m.transition);
}

const matcherText = (/** @type {any} */ m) => (m.event !== undefined ? `event "${m.event}"` : `transition "${m.transition}"`);

/**
 * Why a counterexample run violates a temporal claim, in the words of the trace check.
 * @param {any} ev @param {any[]} steps the steps of the run @param {any} last its final configuration
 * @returns {string}
 */
function temporalWhy(ev, steps, last) {
  if (ev.method === 'never') {
    const i = steps.findIndex((/** @type {any} */ s) => stepHas(ev.occurs, s));
    return `The ${matcherText(ev.occurs)} occurs in step ${i} (time ${steps[i]?.time}), but it was never to occur.`;
  }
  if (ev.method === 'precedes') {
    const same = ev.first.event !== undefined && ev.then.transition !== undefined;
    const i = steps.findIndex((/** @type {any} */ s, /** @type {number} */ k) => stepHas(ev.then, s) && !steps.some((/** @type {any} */ q, /** @type {number} */ j) => (j < k || (same && j === k)) && stepHas(ev.first, q)));
    return `The ${matcherText(ev.then)} occurs in step ${i} with no earlier occurrence of the ${matcherText(ev.first)}.`;
  }
  const parts = [];
  if (ev.occurs !== undefined && !steps.some((/** @type {any} */ s) => stepHas(ev.occurs, s))) parts.push(`The ${matcherText(ev.occurs)} never occurs in the ${steps.length} steps of this run, which ends with nothing left to deliver.`);
  if (ev.expr !== undefined) {
    const parsed = parseExpr(ev.expr);
    if (parsed.ok) {
      try {
        if (evalExpr(parsed.ast, configResolver(last)) === false) parts.push(`\`${ev.expr}\` is false in the final configuration of this run: ${valuesText(parsed.ast, last)}.`);
      } catch (e) { if (!(e instanceof ExprError)) throw e; }
    }
  }
  return parts.join(' ');
}

/**
 * The result of one temporal claim.
 * @param {Model} model @param {ProofPlan} plan @param {any} c @param {any} r @param {Record<string, any>} base
 * @param {string} faultText @param {boolean} withSteps
 */
function temporalResult(model, plan, c, r, base, faultText, withSteps) {
  const ev = c.temporal;
  const runs = `every complete run of the scenario in the behaviour calculus (${faultText}; every order of delivery of simultaneous events; every draw; each run ending with nothing left to deliver or in a failed step)`;
  const what = { never: 'the occurrence never happens', precedes: 'every "then" occurrence has a "first" occurrence before it', eventually: 'the required occurrence happens and the expression holds in the final configuration' }[/** @type {'never'} */ (ev.method)];
  if (r.verdict === 'holds') {
    return { ...base, states: r.states, result: 'holds', explanation: `Verified by Lean over ${runs}: ${what}. ${r.states} distinct search states were visited and the frontier emptied. The temporal meaning is tcheckB_holds (formal/Exegra/ProveB.lean).` };
  }
  if (r.verdict === 'incomplete') {
    return { ...base, states: r.states, result: 'incomplete', explanation: `Nothing is claimed. The search visited ${r.states} distinct states (the budget is ${plan.maxStates}) and stopped before its frontier was empty: the budget or the bound (${plan.bound + 1} steps) cut runs off, or a draw has more outcomes than the explorer tries. A run cut off neither shows nor refutes the claim. Raise --max-states or --bound.` };
  }
  const cex = renderCounterexample(model, plan, r, '', withSteps);
  const last = r.steps.length ? r.steps[r.steps.length - 1].config : r.initial;
  const why = temporalWhy(ev, r.steps, last);
  cex.explanation = why;
  return { ...base, states: null, result: 'counterexample', explanation: `A run of ${cex.stepCount} step${cex.stepCount === 1 ? '' : 's'} violates the claim. ${why} ${cex.faultChoice}`, counterexample: cex };
}

/**
 * The per-claim results of a proof run.
 * @param {Model} model @param {ProofPlan} plan
 * @param {{results: any[]}} explored @param {Map<string, string[]>} axioms
 * @param {{file: string, namespace: string, withSteps?: boolean}} where
 */
export function proofResults(model, plan, explored, axioms, where) {
  const faultText = plan.faults.length
    ? `every subset of the scenario's ${plan.faults.length} fault${plan.faults.length === 1 ? '' : 's'} (${plan.faults.join(', ')})`
    : 'the scenario declares no faults';
  const inputAxioms = axioms.get('input_decodes') ?? [];
  const results = plan.claims.map((c, i) => {
    const r = explored.results[i];
    const theorem = `${where.namespace}.${theoremName(c.claimId)}`;
    const ax = [...new Set([...(axioms.get(c.claimId.replace(/[«»]/g, '')) ?? []), ...inputAxioms])];
    /** @type {Record<string, any>} */
    const base = { claimId: c.claimId, method: PROOF_METHOD, bound: plan.bound, states: r.states ?? null, axioms: ax, theorem, file: where.file, trusted: trustText(ax) };
    if (c.temporal) return temporalResult(model, plan, c, r, base, faultText, where.withSteps === true);
    if (r.verdict === 'holds') {
      return { ...base, result: 'holds', explanation: `Verified by Lean for every reachable configuration of the scenario in the behaviour calculus, over every order of delivery of simultaneous events, ${faultText} and every draw: \`${c.expr}\` holds in each and no run fails. The search visited ${r.states} distinct calculus states and its frontier emptied within ${plan.bound} step${plan.bound === 1 ? '' : 's'}, so the result has no bound (explore_holds_invariant).` };
    }
    if (r.verdict === 'incomplete') {
      return { ...base, result: 'incomplete', explanation: `Nothing is claimed. The search visited ${r.states} distinct calculus states (the budget is ${plan.maxStates}) and stopped before its frontier was empty: the budget or the bound (${plan.bound} steps) was reached, or a draw has more outcomes than the explorer tries. Raise --max-states or --bound.` };
    }
    const cex = renderCounterexample(model, plan, r, c.expr, where.withSteps === true);
    return { ...base, states: null, result: 'counterexample', explanation: `A run of ${cex.stepCount} step${cex.stepCount === 1 ? '' : 's'} violates the invariant. ${cex.explanation} ${cex.faultChoice}`, counterexample: cex };
  });
  return [...results, ...plan.skipped];
}
