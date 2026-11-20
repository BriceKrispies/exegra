// Inputs a request supplies from its address or its session, not from its body (WG-4968, item 3 of the format gaps
// of WG-4939). docs/model-and-format.md, "Supplied inputs".
//
// A contract served over HTTP takes some inputs from the body and others from the request itself: the tenant the
// host or path names (route), the signed-in context (session). binding.suppliedBy states which: {input: "route" |
// "session"}. Such an input is never read from the body, so a body that carries it is refused by the generated
// route, and no form field or action argument of the user interface may fill it (form.supplied-input,
// action.supplied-input, checked in src/core/ui.js).
//
// Consistency rule (error, always on):
//   contract.supplied-by   suppliedBy is an object from declared input names to route or session

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** Where a supplied input comes from. */
export const SUPPLIERS = Object.freeze(['route', 'session']);

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/**
 * The inputs of a contract that its request supplies: input name -> route or session. Entries that are not
 * well formed are left out (contract.supplied-by reports them).
 * @param {Entity|undefined} contract @returns {Map<string, string>}
 */
export function suppliedInputs(contract) {
  /** @type {Map<string, string>} */
  const out = new Map();
  const s = contract?.data.binding?.suppliedBy;
  if (!isObj(s)) return out;
  const names = new Set((Array.isArray(contract?.data.inputs) ? contract.data.inputs : []).filter(isObj).map((i) => i.name));
  for (const [name, from] of Object.entries(s)) if (names.has(name) && SUPPLIERS.includes(/** @type {string} */ (from))) out.set(name, /** @type {string} */ (from));
  return out;
}

/**
 * The consistency rule of supplied inputs.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkSuppliedInputs(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const c of model.byKind.contract ?? []) {
    const s = c.data.binding?.suppliedBy;
    if (s === undefined) continue;
    /** @param {string} message @param {(string|number)[]} [at] */
    const err = (message, at = []) => out.push({ code: 'contract.supplied-by', severity: 'error', message, entityId: c.id, loc: c.loc, path: [...c.path, 'binding', 'suppliedBy', ...at] });
    if (!isObj(s)) { err(`The "suppliedBy" of contract "${c.id}" is an object from input names to ${SUPPLIERS.join(' or ')}.`); continue; }
    const names = new Set((Array.isArray(c.data.inputs) ? c.data.inputs : []).filter(isObj).map((i) => i.name));
    for (const [name, from] of Object.entries(s)) {
      if (!names.has(name)) err(`Contract "${c.id}" says "${name}" is supplied by its request, but has no input of that name.`, [name]);
      else if (!SUPPLIERS.includes(from)) err(`Input "${name}" of contract "${c.id}" is supplied by ${JSON.stringify(from)}; it is ${SUPPLIERS.join(' or ')}.`, [name]);
    }
  }
  return out;
}
