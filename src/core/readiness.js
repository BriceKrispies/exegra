// Generation readiness: what a specification must state before code is generated from it. Each rule is a
// function of the model returning diagnostics with a `ready.*` code. When the specification sets
// `system.generation` validate reports them as errors; otherwise only the `readiness` command lists them.

import { errorStatus, typeResolves } from './codegen-model.js';
import { machineReadiness } from './readiness-machines.js';
import { constructReadiness } from './constructs.js';
import { uiReadiness } from './ui.js';
import { telemetryReadiness } from './telemetry.js';
import { languageReadiness } from './language.js';
import { functionReadiness } from './function.js';
import { derivationReadiness } from './derivation.js';
import { functionBranchReadiness } from './function-coverage.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {{code: string, severity: 'error' | 'info', message: string, entityId: string}} Gap */

const HOLE_REF_RE = /^H-\d{1,4}$/;

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/** @param {Entity} e @param {string} code @param {string} message @returns {Gap} */
const gap = (e, code, message) => ({ code, severity: 'error', message, entityId: e.id });

/** @param {any} type */
const unresolvedText = (type) => (type === undefined ? 'no type' : `type "${type}", which is neither built-in nor a declared type`);

/** Records: field types resolve, every reference says what deletion does, a schema version. @param {Model} model @returns {Gap[]} */
function recordReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  for (const r of model.byKind.record ?? []) {
    for (const f of Array.isArray(r.data.fields) ? r.data.fields : []) {
      if (!isObj(f)) continue;
      if (!typeResolves(model, f.type)) out.push(gap(r, 'ready.field-type-undeclared', `Field "${f.name}" of record "${r.id}" has ${unresolvedText(f.type)}.`));
      if (f.refersTo !== undefined && f.onDelete === undefined) out.push(gap(r, 'ready.on-delete-missing', `Field "${f.name}" of record "${r.id}" refers to "${f.refersTo}" but says nothing about what deleting it does ("onDelete").`));
    }
    if (r.data.schemaVersion === undefined) out.push(gap(r, 'ready.schema-version-missing', `Record "${r.id}" states no schemaVersion.`));
  }
  return out;
}

/** Contracts: declared types, a realisation, and the three things a hole needs. @param {Model} model @returns {Gap[]} */
function contractReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  for (const c of model.byKind.contract ?? []) {
    for (const [prop, what, code] of /** @type {const} */ ([['inputs', 'input', 'ready.contract-input-type-undeclared'], ['outputs', 'output', 'ready.contract-output-type-undeclared']])) {
      for (const f of Array.isArray(c.data[prop]) ? c.data[prop] : []) {
        if (isObj(f) && !typeResolves(model, f.type)) out.push(gap(c, code, `The ${what} "${f.name}" of contract "${c.id}" has ${unresolvedText(f.type)}.`));
      }
    }
    // An error carries a payload type only when it has one.
    for (const f of Array.isArray(c.data.errors) ? c.data.errors : []) {
      if (isObj(f) && f.type !== undefined && !typeResolves(model, f.type)) out.push(gap(c, 'ready.contract-error-type-undeclared', `The error "${f.name}" of contract "${c.id}" has ${unresolvedText(f.type)}.`));
    }
    // A contract a component serves answers each error with a status; with an error body, with a kind.
    if (c.data.implementedBy !== undefined) {
      const g = isObj(model.system.data.generation) ? model.system.data.generation : {};
      for (const f of Array.isArray(c.data.errors) ? c.data.errors : []) {
        if (!isObj(f)) continue;
        if (isObj(g.errorBody)) {
          if (f.kind === undefined && g.errorKind === undefined) out.push(gap(c, 'ready.error-kind-missing', `The error "${f.name}" of contract "${c.id}" states no "kind" and system.generation states no errorKind, so the error body cannot say what kind of failure it is.`));
        } else if (errorStatus(model, f) === undefined) out.push(gap(c, 'ready.error-status-missing', `The error "${f.name}" of contract "${c.id}" states no "status" or "kind", and system.generation states no errorStatus or errorKind, so nothing says which HTTP status it is answered with.`));
      }
    }
    if (c.data.realisation === undefined) out.push(gap(c, 'ready.contract-realisation-missing', `Contract "${c.id}" does not say how it is realised ("realisation": generated, derived, facade or hand).`));
    if (c.data.realisation === 'hand') {
      if (typeof c.data.ref !== 'string' || !HOLE_REF_RE.test(c.data.ref)) out.push(gap(c, 'ready.hole-ref-invalid', `Hand-written contract "${c.id}" needs a "ref" such as H-012; found ${c.data.ref === undefined ? 'none' : `"${c.data.ref}"`}.`));
      if (c.data.implementedBy === undefined) out.push(gap(c, 'ready.hole-implemented-by-missing', `Hand-written contract "${c.id}" names no component in "implementedBy".`));
      if (!(Array.isArray(c.data.postconditions) && c.data.postconditions.length)) out.push(gap(c, 'ready.hole-postcondition-missing', `Hand-written contract "${c.id}" states no postcondition, so nothing says what its implementation must do.`));
    }
  }
  return out;
}

/** Events: payload field types resolve. @param {Model} model @returns {Gap[]} */
function eventReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  for (const e of model.byKind.event ?? []) {
    for (const f of Array.isArray(e.data.payload) ? e.data.payload : []) {
      if (isObj(f) && !typeResolves(model, f.type)) out.push(gap(e, 'ready.event-payload-type-undeclared', `Payload field "${f.name}" of event "${e.id}" has ${unresolvedText(f.type)}.`));
    }
  }
  return out;
}

/** Requirements: each says how it is realised. @param {Model} model @returns {Gap[]} */
function requirementReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  for (const c of model.byKind.claim ?? []) {
    if (c.data.kind === 'requirement' && c.data.realisation === undefined) out.push(gap(c, 'ready.requirement-realisation-missing', `Requirement "${c.id}" does not say how it is realised ("realisation": construction, checked or operational).`));
  }
  return out;
}

/**
 * Functions: the examples readiness asks for (ready.function-example-missing), then the branches no example takes
 * (ready.function-branch-uncovered), which is not reported for a function that still misses an example.
 * @param {Model} model @returns {Gap[]}
 */
function functionRules(model) {
  const missing = functionReadiness(model);
  return [...missing, ...functionBranchReadiness(model, { missing: new Set(missing.map((g) => g.entityId)) })];
}

/**
 * The readiness rules that apply only when the specification sets system.generation, each a function of
 * the model. The machine rules (machineReadiness) are not here: validate reports them for every
 * implementation-level behavior whether the switch is set or not.
 * @type {((model: Model) => Gap[])[]}
 */
export const READINESS_RULES = [recordReadiness, contractReadiness, eventReadiness, requirementReadiness, constructReadiness, uiReadiness, telemetryReadiness, languageReadiness, functionRules, derivationReadiness];

/** Every readiness gap of the model: the switch-gated rules, then the machine rules. @param {Model} model @returns {Gap[]} */
export function readinessGaps(model) {
  return [...READINESS_RULES.flatMap((rule) => rule(model)), .../** @type {Gap[]} */ (machineReadiness(model))];
}
