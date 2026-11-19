// Whether a machine or a contract models code that exists ("shipped") or the enterprise target ("target"),
// and where a machine lives ("record" or "memory") (docs/semantics.md, "Realisation and durability").

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

/**
 * The component a behavior's or contract's realisation follows: a behavior's subject, a contract's implementedBy.
 * @param Model} model @param {Entity} e
 */
function owningComponent(model, e) {
  const id = e.kind === 'behavior' ? e.data.subject : e.kind === 'contract' ? e.data.implementedBy : undefined;
  const c = typeof id === 'string' ? model.entities.get(id) : undefined;
  return c && c.kind === 'component' ? c : undefined;
}

/**
 * The declared value (behavior.realisation, contract.deployment) or, when absent, the default: "target" when the
 * owning component has implementation.status "not-implemented", otherwise "shipped".
 * @param Model} model @param {Entity} e
 * @returns {'shipped' | 'target'}
 */
export function effectiveRealisation(model, e) {
  const declared = e.kind === 'behavior' ? e.data.realisation : e.data.deployment;
  if (declared === 'shipped' || declared === 'target') return declared;
  return notImplemented(model, e) ? 'target' : 'shipped';
}

/** True when the component the entity follows is declared not-implemented. @param Model} model @param {Entity} e */
export function notImplemented(model, e) {
  const c = owningComponent(model, e);
  return !!c && /** @type {any} */ (c.data).implementation?.status === 'not-implemented';
}

/** The effective durability of a machine: "record" unless storage.durability says "memory". @param {Entity} b @returns {'record' | 'memory'} */
export function effectiveDurability(b) {
  return b.data.storage && typeof b.data.storage === 'object' && b.data.storage.durability === 'memory' ? 'memory' : 'record';
}
