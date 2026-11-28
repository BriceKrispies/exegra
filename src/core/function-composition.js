// Functional composition along the hierarchy (WG-5730; docs/assessment/2026-11-27/multiscale.md, the compiler case
// study). A `function` entity attaches to an element (function.element). A function attached to a composite
// element may declare function.composition: the ordered stages, each a function attached to a member of that
// element, that it is the composition of. The signature the composite declares must equal the composition of its
// stages' signatures:
//
//   params    the parameters of the first stage, name for name and type for type;
//   returns   the returns of the last stage;
//   chain     every later stage takes exactly one parameter, of the type the stage before it returns;
//   errors    the stages that declare an error union share one, and the composite declares that union (or none,
//             when no stage declares one).
//
// A stage may itself be a composite with its own declared composition, so the rule is checked at every level of
// the hierarchy: a composite's declared signature stands for the composition below it. Types are compared as
// written, without white space. This is a pure projection of the specification (no function is run), so it
// decides nothing the verified kernel decides.

import { LOGICAL, hierarchyOf } from './query.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {{name: string, type: string}} ParamSig */
/** @typedef {{params: ParamSig[], returns: string|null, errors: string|null}} Signature */
/** @typedef {{code: string, message: string, path: (string|number)[]}} Problem */

/** @param {any} v @returns {string} */
const norm = (v) => (typeof v === 'string' ? v.replace(/\s+/g, '') : '');
/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/**
 * The signature a function declares, as written.
 * @param {Entity} fn @returns {Signature}
 */
export function signatureOf(fn) {
  const d = fn.data;
  const params = (Array.isArray(d.params) ? d.params : []).filter(isObj).map((/** @type {any} */ p) => ({ name: String(p.name ?? ''), type: norm(p.type) }));
  return { params, returns: typeof d.returns === 'string' ? norm(d.returns) : null, errors: typeof d.errors === 'string' ? d.errors : null };
}

/** @param {ParamSig[]} params */
const paramsText = (params) => `(${params.map((p) => `${p.name}: ${p.type}`).join(', ')})`;

/** The element a function is attached to, or null. @param {Model} model @param {Entity} fn */
function elementOfFunction(model, fn) {
  const e = typeof fn.data.element === 'string' ? model.entities.get(fn.data.element) : undefined;
  return e && (e.kind === 'component' || e.kind === 'system') ? e.id : null;
}

/** @param {Model} model @param {string} id @returns {string[]} */
function stagesOf(model, id) {
  const f = model.entities.get(id);
  const st = f?.kind === 'function' && isObj(f.data.composition) && Array.isArray(f.data.composition.stages) ? f.data.composition.stages : [];
  return st.filter((/** @type {any} */ x) => typeof x === 'string');
}

/** Whether following composition stages from a function leads back to it. @param {Model} model @param {string} id */
function reachesItself(model, id) {
  const seen = new Set();
  const stack = stagesOf(model, id).filter((s) => s !== id);
  while (stack.length) {
    const x = /** @type {string} */ (stack.pop());
    if (x === id) return true;
    if (seen.has(x)) continue;
    seen.add(x);
    stack.push(...stagesOf(model, x));
  }
  return false;
}

/** @param {string} a @param {string} b */
const byText = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

/**
 * Every function attached to an element, and every declared composition checked: the stages with their signatures,
 * the signature the composition derives, and what disagrees with the declared one. `holds` is true exactly when
 * nothing is wrong.
 * @param {Model} model
 * @returns {{attached: {function: string, element: string}[], composites: {function: string, element: string|null, stages: {function: string, element: string|null, signature: Signature}[], declared: Signature, derived: Signature|null, holds: boolean, problems: Problem[]}[]}}
 */
export function functionComposition(model) {
  const h = hierarchyOf(model, LOGICAL);
  const functions = model.byKind.function ?? [];
  const attached = functions.flatMap((f) => { const e = elementOfFunction(model, f); return e ? [{ function: f.id, element: e }] : []; })
    .sort((a, b) => byText(a.element, b.element) || byText(a.function, b.function));
  /** @type {ReturnType<typeof functionComposition>['composites']} */
  const composites = [];
  for (const f of functions) {
    if (!isObj(f.data.composition)) continue;
    const element = elementOfFunction(model, f);
    const declared = signatureOf(f);
    /** @type {Problem[]} */
    const problems = [];
    const stageIds = Array.isArray(f.data.composition.stages) ? f.data.composition.stages : [];
    if (!element) problems.push({ code: 'function.composition-element', message: `Function "${f.id}" declares a composition but is attached to no element; a composition is of the member elements of the element it is the function of (function.element).`, path: ['element'] });
    if (!stageIds.length) problems.push({ code: 'function.composition-stage', message: `The composition of function "${f.id}" lists no stages.`, path: ['composition', 'stages'] });
    /** @type {{function: string, element: string|null, signature: Signature}[]} */
    const stages = [];
    stageIds.forEach((/** @type {any} */ id, /** @type {number} */ i) => {
      const s = typeof id === 'string' ? model.entities.get(id) : undefined;
      const at = ['composition', 'stages', i];
      if (!s || s.kind !== 'function') { problems.push({ code: 'function.composition-stage', message: `Stage ${i + 1} of the composition of function "${f.id}", ${JSON.stringify(id)}, is not a function.`, path: at }); return; }
      const el = elementOfFunction(model, s);
      if (s.id === f.id) problems.push({ code: 'function.composition-cycle', message: `Function "${f.id}" is a stage of its own composition.`, path: at });
      else if (!el) problems.push({ code: 'function.composition-stage', message: `Stage ${i + 1} of the composition of function "${f.id}", "${s.id}", is attached to no element, so it is not a function of a member of "${element ?? '?'}".`, path: at });
      else if (element && h && h.parent.get(el) !== element) problems.push({ code: 'function.composition-stage', message: `Stage ${i + 1} of the composition of function "${f.id}", "${s.id}", is attached to "${el}", which is not a member of "${element}" in the logical hierarchy.`, path: at });
      stages.push({ function: s.id, element: el, signature: signatureOf(s) });
    });
    if (reachesItself(model, f.id)) problems.push({ code: 'function.composition-cycle', message: `The composition of function "${f.id}" reaches "${f.id}" again through its stages.`, path: ['composition', 'stages'] });

    /** @type {Signature|null} */
    let derived = null;
    if (stages.length && stages.length === stageIds.length) {
      const first = stages[0].signature;
      const lastStage = stages[stages.length - 1];
      stages.slice(1).forEach((st, k) => {
        const prev = stages[k];
        const at = ['composition', 'stages', k + 1];
        if (st.signature.params.length !== 1) problems.push({ code: 'function.composition-arity', message: `Stage ${k + 2} of the composition of function "${f.id}", "${st.function}", takes ${st.signature.params.length} parameters; a stage after the first takes exactly the one value the stage before it returns.`, path: at });
        else if (prev.signature.returns !== st.signature.params[0].type) problems.push({ code: 'function.composition-chain', message: `Stage ${k + 1} ("${prev.function}") returns ${prev.signature.returns ?? '?'} but stage ${k + 2} ("${st.function}") takes ${st.signature.params[0].type}; the stages of "${f.id}" do not compose.`, path: at });
      });
      const errorSets = [...new Set(stages.map((s) => s.signature.errors).filter((e) => e !== null))];
      if (errorSets.length > 1) problems.push({ code: 'function.composition-errors', message: `The stages of function "${f.id}" fail with different error unions (${errorSets.join(', ')}); the stages of a composition share one.`, path: ['composition', 'stages'] });
      const errors = errorSets.length === 1 ? errorSets[0] : null;
      derived = { params: first.params, returns: lastStage.signature.returns, errors };
      const sameParams = declared.params.length === first.params.length && declared.params.every((p, i) => p.name === first.params[i].name && p.type === first.params[i].type);
      if (!sameParams) problems.push({ code: 'function.composition-params', message: `Function "${f.id}" declares the parameters ${paramsText(declared.params)}, but its first stage "${stages[0].function}" takes ${paramsText(first.params)}; the composition takes the parameters of its first stage.`, path: ['params'] });
      if (declared.returns !== derived.returns) problems.push({ code: 'function.composition-returns', message: `Function "${f.id}" declares that it returns ${declared.returns ?? '?'}, but its last stage "${lastStage.function}" returns ${derived.returns ?? '?'}; the composition returns what its last stage returns.`, path: ['returns'] });
      if (errorSets.length <= 1 && declared.errors !== errors) problems.push({ code: 'function.composition-errors', message: `Function "${f.id}" declares the errors ${declared.errors ?? 'none'}, but its stages fail with ${errors ?? 'none'}; the composition fails with the union its stages share.`, path: ['errors'] });
    }
    composites.push({ function: f.id, element, stages, declared, derived, holds: problems.length === 0, problems });
  }
  composites.sort((a, b) => byText(a.function, b.function));
  return { attached, composites };
}

/**
 * The validation findings of functional composition: each composition problem is an error at the composite function;
 * a function attached to an element whose members carry functions, with no composition declared, is a warning.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkFunctionComposition(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  const { attached, composites } = functionComposition(model);
  for (const c of composites) {
    const fn = /** @type {Entity} */ (model.entities.get(c.function));
    for (const p of c.problems) out.push({ code: p.code, severity: 'error', message: p.message, entityId: fn.id, loc: fn.loc, path: [...fn.path, ...p.path] });
  }
  const h = hierarchyOf(model, LOGICAL);
  const withFunctions = new Set(attached.map((a) => a.element));
  const declared = new Set(composites.map((c) => c.function));
  for (const a of attached) {
    if (declared.has(a.function) || !h) continue;
    if ((h.children.get(a.element) ?? []).some((m) => withFunctions.has(m))) {
      const fn = /** @type {Entity} */ (model.entities.get(a.function));
      out.push({ code: 'function.composition-missing', severity: 'warning', message: `Function "${a.function}" is attached to "${a.element}", whose members carry functions, but declares no composition; state the stages it is composed of, so its signature is checked against theirs.`, entityId: fn.id, loc: fn.loc, path: fn.path });
    }
  }
  return out;
}
