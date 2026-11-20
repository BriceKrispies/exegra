// Derived and facade contracts (WG-4935, NC-4 and NC-5 of WG-4895). docs/model-and-format.md, "Derived and facade
// contracts".
//
// A contract with realisation "derived" states how its implementation is built from functions (src/core/function.js)
// and other contracts, in contract.derivation:
//   pure     {kind, function}: the implementation is the function.
//   read     {kind, needs, load, decide}: needs gives the list of needs from the inputs, the load contract loads them,
//            decide gives the outputs from the inputs and what was loaded. A read may also name insufficient and
//            needRounds (both or neither): the need loop of a command, without a commit (WG-4939: a store's query
//            loads the schema before it knows what a named query needs).
//   command  {kind, needs, load, decide, commit, conflict, insufficient, needRounds, retries}: the load-decide-commit
//            loop of a store: while decide fails with the insufficient variant (carrying one more need) and fewer than
//            needRounds extra needs were asked for, the need is added and loaded; then the commit contract commits
//            what decide gave; while it fails with the conflict error and fewer than retries commits were retried, the
//            whole decision starts over.
// A read or command may also state header: true (WG-4968). Storage-api's execute loads once with no needs (the header: the
// schema, members and counters every load holds), computes the needs from what that gave, and loads them together in
// one round; only the extra needs decide asks for count against needRounds. With header the load contract is first
// called with an empty list of needs, and its outputs are parameters of the needs function as well as of decide.
// Every kind may name fault: the contract error an integer overflow or a division by zero in a function becomes.
//
// Values are matched by name and type: a function parameter is an input of the contract (or, for decide, an output
// of the load contract) of the same name and type; an input of the load or commit contract is filled the same way,
// or by type from the needs list (load) or what decide gives (commit). An optional field of type T has the type
// option<T>. Error variants and contract errors are matched by their words (VersionConflict is version-conflict);
// a contract error with a payload type matches a newtype variant of that type, one without a unit variant.
//
// A contract with realisation "target" is specified but not yet implemented (WG-4968): nothing serves it, so no
// derivation loads or commits through it and no facade is lowered onto it.
//
// A contract with realisation "facade" has no server implementation: a client lowers it onto a generic contract. It
// states a bffRoute "<METHOD> <path> <shape> ..." (a property the specification declares in its vocabulary), and
// exactly one served contract (not a facade, with implementedBy) states a bffRoute of the same method, path and
// shape.
//
// Consistency rules (errors, always on; each contract reports its first finding):
//   derivation.kind        a derivation exactly on a derived contract, of a known kind, with the fields of that kind
//   derivation.signature   the functions fit the contract's inputs, outputs and errors
//   derivation.load        the load contract can be called from the inputs and the needs, and its outputs and errors fit
//   derivation.commit      the commit contract can be called, its conflict error exists, and its outputs and errors fit
//   derivation.bounds      needRounds and retries (a read's needRounds) are stated, as non-negative integers
//   contract.facade-route  a facade has no implementing component and its bffRoute names exactly one served contract
// Readiness (errors when system.generation is set, listed by the readiness command otherwise):
//   ready.derived-function-missing  every function a derivation names is declared

import { analyzeFunctions, runFunction } from './function.js';
import { valueEq } from './function-value.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {{code: string, severity: 'error', message: string, entityId: string}} Gap */

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);

/** The fields each kind takes, besides kind and fault. */
export const DERIVATION_KINDS = Object.freeze({
  pure: ['function'],
  read: ['needs', 'load', 'decide'],
  command: ['needs', 'load', 'decide', 'commit', 'conflict', 'insufficient', 'needRounds', 'retries'],
});
/** The fields a kind may take besides those it needs: a read's need loop, named together or not at all. */
export const OPTIONAL_DERIVATION_FIELDS = Object.freeze({ pure: [], read: ['insufficient', 'needRounds', 'header'], command: ['header'] });
/** The fields of a read's need loop, named together or not at all. */
const NEED_LOOP = ['insufficient', 'needRounds'];
/** The fields of a derivation that name functions. */
const FUNCTION_FIELDS = ['function', 'needs', 'decide'];
/** Which code a missing field is reported with. */
const MISSING_CODE = /** @type {Record<string, string>} */ ({
  load: 'derivation.load', commit: 'derivation.commit', conflict: 'derivation.commit', needRounds: 'derivation.bounds', retries: 'derivation.bounds',
});

/** The words of a name, lower case, joined by "-": VersionConflict and version-conflict are both version-conflict. @param {string} name */
export function wordsOf(name) {
  const out = [];
  for (const run of String(name).split(/[^A-Za-z0-9]+/)) {
    let word = '';
    for (let i = 0; i < run.length; i++) {
      const c = run[i], prev = run[i - 1], next = run[i + 1];
      const lowerToUpper = i > 0 && /[a-z0-9]/.test(prev) && /[A-Z]/.test(c);
      const acronymEnd = i > 0 && /[A-Z]/.test(prev) && /[A-Z]/.test(c) && next !== undefined && /[a-z]/.test(next);
      if ((lowerToUpper || acronymEnd) && word) { out.push(word); word = ''; }
      word += c.toLowerCase();
    }
    if (word) out.push(word);
  }
  return out.join('-');
}

/** A type text without white space. @param {any} t */
const norm = (t) => (typeof t === 'string' ? t.replace(/\s+/g, '') : '');
/** The type of a field: option<T> when it is optional. @param {any} f */
const fieldType = (f) => (f.optional === true ? `option<${norm(f.type)}>` : norm(f.type));
/** @param {any[]} fields @returns {Map<string, string>} */
const typesByName = (fields) => new Map(list(fields).filter(isObj).map((f) => [f.name, fieldType(f)]));

/** The element type of list<T>, or undefined. @param {string} t */
const listItem = (t) => { const m = /^list<(.+)>$/.exec(t); return m ? m[1] : undefined; };

/** A route "<METHOD> <path> <shape> ...": the method, path and shape, or undefined. @param {any} route */
export function routeShape(route) {
  if (typeof route !== 'string') return undefined;
  const parts = route.trim().split(/\s+/);
  if (parts.length < 3 || !/^(GET|POST|PUT|PATCH|DELETE)$/.test(parts[0]) || !parts[1].startsWith('/')) return undefined;
  return { method: parts[0], path: parts[1], shape: parts[2] };
}

class Finding extends Error {
  /** @param {string} code @param {string} message @param {(string|number)[]} [at] */
  constructor(code, message, at = []) {
    super(message);
    this.code = code;
    this.at = at;
  }
}

/**
 * @param {Model} model @param {any} id
 * @returns {{id: string, params: any[], returns: string, errors: Entity|undefined}|undefined} undefined when no such function
 */
function fnOf(model, id) {
  const f = typeof id === 'string' ? model.entities.get(id) : undefined;
  if (!f || f.kind !== 'function') return undefined;
  const errors = typeof f.data.errors === 'string' ? model.entities.get(f.data.errors) : undefined;
  return { id: f.id, params: list(f.data.params).filter(isObj), returns: norm(f.data.returns), errors: errors?.kind === 'type' ? errors : undefined };
}

/** @param {Model} model @param {string} t @returns {any|undefined} the declared type of a type text */
const typeDecl = (model, t) => { const e = model.entities.get(t); return e?.kind === 'type' ? e.data : undefined; };

/**
 * Every error of `variants` (the variants of a union, or the errors of a contract) is an error of `c` with the same
 * payload; the first that is not, as text, or undefined.
 * @param {Entity} c @param {{name: string, type: string|undefined}[]} errs @param {string} what
 */
function errorsFit(c, errs, what) {
  const mine = new Map(list(c.data.errors).filter(isObj).map((e) => [wordsOf(e.name), e]));
  for (const e of errs) {
    const target = mine.get(wordsOf(e.name));
    if (!target) return `${what} "${e.name}" is not an error of contract "${c.id}"`;
    const want = target.type === undefined ? undefined : norm(target.type);
    if (want !== e.type) {
      return `${what} "${e.name}" ${e.type === undefined ? 'carries no payload' : `carries ${e.type}`}, but the error "${target.name}" of contract "${c.id}" ${want === undefined ? 'carries none' : `carries ${want}`}`;
    }
  }
  return undefined;
}

/** The variants of a union as errors: a newtype carries its field's type, a unit variant none. @param {any} union */
function variantErrors(union) {
  return list(union?.variants).filter(isObj).map((v) => {
    const fields = list(v.fields).filter(isObj);
    if (!fields.length) return { name: v.name, type: undefined, shape: 'unit' };
    if (v.newtype === true && fields.length === 1) return { name: v.name, type: fieldType(fields[0]), shape: 'newtype' };
    return { name: v.name, type: undefined, shape: 'fields' };
  });
}

/** @param {Model} model @param {NonNullable<ReturnType<typeof fnOf>>} f @param {string} role */
function fnErrors(model, f, role) {
  if (!f.errors) return [];
  const vs = variantErrors(f.errors.data);
  const bad = vs.find((v) => v.shape === 'fields');
  if (bad) throw new Finding('derivation.signature', `Variant "${bad.name}" of "${f.errors.id}", the errors of function "${f.id}" (${role}), has named fields; a variant that becomes a contract error is a unit variant or a newtype of the error's payload type.`, [role]);
  return vs.map((v) => ({ name: v.name, type: v.type }));
}

/** Each parameter of `f` is in `scope` with the same type. @param {NonNullable<ReturnType<typeof fnOf>>} f @param {Map<string, string>} scope @param {string} role @param {string} where */
function paramsFit(f, scope, role, where) {
  for (const p of f.params) {
    const t = scope.get(p.name);
    if (t === undefined) throw new Finding('derivation.signature', `Parameter "${p.name}" of function "${f.id}" (${role}) is not ${where}.`, [role]);
    if (t !== norm(p.type)) throw new Finding('derivation.signature', `Parameter "${p.name}" of function "${f.id}" (${role}) is ${norm(p.type)}, but the "${p.name}" it is given (${where}) is ${t}.`, [role]);
  }
}

/** What `f` gives is the contract's outputs: the one output's type, or a struct with exactly the outputs as fields. @param {Model} model @param {Entity} c @param {NonNullable<ReturnType<typeof fnOf>>} f @param {string} role */
function returnsFit(model, c, f, role) {
  const outs = list(c.data.outputs).filter(isObj);
  if (outs.length === 1 && fieldType(outs[0]) === f.returns) return;
  const decl = typeDecl(model, f.returns);
  if (decl?.kind === 'struct') {
    const fields = typesByName(decl.fields);
    const wanted = typesByName(outs);
    if (fields.size === wanted.size && [...wanted].every(([n, t]) => fields.get(n) === t)) return;
  }
  throw new Finding('derivation.signature', `Function "${f.id}" (${role}) gives ${f.returns || 'nothing'}, which is neither the type of the one output of contract "${c.id}" nor a struct whose fields are exactly its outputs (${outs.map((o) => `${o.name}: ${fieldType(o)}`).join(', ') || 'none'}).`, [role]);
}

/** A contract that a derivation calls: not a facade, not the contract itself. @param {Model} model @param {Entity} c @param {any} id @param {string} role */
function calledContract(model, c, id, role) {
  const code = role === 'load' ? 'derivation.load' : 'derivation.commit';
  const e = typeof id === 'string' ? model.entities.get(id) : undefined;
  // An unresolved reference is reported by the parser (ref.unresolved, ref.kind).
  if (!e || e.kind !== 'contract') return undefined;
  if (e.id === c.id) throw new Finding(code, `Contract "${c.id}" names itself as its ${role} contract.`, [role]);
  if (e.data.realisation === 'facade') throw new Finding(code, `The ${role} contract "${e.id}" of contract "${c.id}" is a facade, which nothing serves.`, [role]);
  if (e.data.realisation === 'target') throw new Finding(code, `The ${role} contract "${e.id}" of contract "${c.id}" is a target, which nothing implements yet.`, [role]);
  return e;
}

/**
 * Fills the inputs of a called contract: each required input by name from `scope` (same type), else by type with
 * `extra` (the needs list or what decide gives), which must fill exactly one input.
 * @param {Entity} c @param {Entity} called @param {Map<string, string>} scope @param {{type: string, what: string}} extra @param {string} role
 */
function inputsFit(c, called, scope, extra, role) {
  const code = role === 'load' ? 'derivation.load' : 'derivation.commit';
  let taken = 0;
  for (const i of list(called.data.inputs).filter(isObj)) {
    const t = fieldType(i);
    if (scope.has(i.name) && scope.get(i.name) === t) continue;
    if (t === extra.type) { taken++; continue; }
    if (i.optional === true) continue;
    throw new Finding(code, `Input "${i.name}" (${t}) of the ${role} contract "${called.id}" is neither ${role === 'load' ? `an input of contract "${c.id}"` : `an input of contract "${c.id}" or an output of its load contract`} of that name and type, nor ${extra.what} (${extra.type}).`, [role]);
  }
  if (taken !== 1) throw new Finding(code, `${taken ? 'Several inputs' : 'No input'} of the ${role} contract "${called.id}" take${taken ? '' : 's'} ${extra.what} (${extra.type}); exactly one must.`, [role]);
}

/** @param {Model} model @param {Entity} c @param {any} d */
function checkDerived(model, c, d) {
  if (!isObj(d)) throw new Finding('derivation.kind', `Contract "${c.id}" is derived and needs "derivation": {kind: pure | read | command, ...}.`);
  const kind = d.kind;
  if (!Object.hasOwn(DERIVATION_KINDS, kind)) throw new Finding('derivation.kind', `The derivation of contract "${c.id}" has kind ${JSON.stringify(kind)}; it is pure, read or command.`, ['kind']);
  const takes = /** @type {readonly string[]} */ (DERIVATION_KINDS[/** @type {keyof typeof DERIVATION_KINDS} */ (kind)]);
  const optional = /** @type {readonly string[]} */ (OPTIONAL_DERIVATION_FIELDS[/** @type {keyof typeof DERIVATION_KINDS} */ (kind)]);
  for (const k of Object.keys(d)) {
    if (k !== 'kind' && k !== 'fault' && !takes.includes(k) && !optional.includes(k)) throw new Finding('derivation.kind', `A ${kind} derivation takes no "${k}" (contract "${c.id}"); it takes ${[...takes, ...optional].join(', ')}.`, [k]);
  }
  for (const k of takes) {
    if (d[k] === undefined) throw new Finding(MISSING_CODE[k] ?? 'derivation.kind', `The ${kind} derivation of contract "${c.id}" needs "${k}".`);
  }
  // A read's need loop: insufficient and needRounds together.
  const loops = kind === 'command' || (kind === 'read' && (d.insufficient !== undefined || d.needRounds !== undefined));
  if (kind === 'read' && loops) {
    for (const k of NEED_LOOP) {
      if (d[k] === undefined) throw new Finding(MISSING_CODE[k] ?? 'derivation.kind', `The read derivation of contract "${c.id}" names ${k === 'needRounds' ? '"insufficient"' : '"needRounds"'}, so it needs "${k}" too: a read's need loop names both.`);
    }
  }
  for (const k of FUNCTION_FIELDS) {
    if (d[k] !== undefined && (typeof d[k] !== 'string' || !d[k])) throw new Finding('derivation.kind', `"${k}" of the derivation of contract "${c.id}" is the id of a function.`, [k]);
  }
  const errs = new Map(list(c.data.errors).filter(isObj).map((e) => [e.name, e]));
  if (d.fault !== undefined) {
    const e = errs.get(d.fault);
    if (!e) throw new Finding('derivation.signature', `"fault" of contract "${c.id}" names "${d.fault}", which is not one of its errors.`, ['fault']);
    if (e.type !== undefined) throw new Finding('derivation.signature', `The fault error "${d.fault}" of contract "${c.id}" carries ${norm(e.type)}; a fault carries no payload.`, ['fault']);
  }
  if (loops) {
    for (const k of kind === 'command' ? ['needRounds', 'retries'] : ['needRounds']) {
      if (!Number.isInteger(d[k]) || d[k] < 0) throw new Finding('derivation.bounds', `"${k}" of the derivation of contract "${c.id}" is ${JSON.stringify(d[k])}; it is a non-negative integer.`, [k]);
    }
  }
  // A function that is not declared is a readiness gap (ready.derived-function-missing): nothing more can be checked.
  const fns = FUNCTION_FIELDS.filter((k) => d[k] !== undefined).map((k) => fnOf(model, d[k]));
  if (fns.some((f) => f === undefined)) return;

  const inputs = typesByName(c.data.inputs);
  if (kind === 'pure') {
    const f = /** @type {NonNullable<ReturnType<typeof fnOf>>} */ (fnOf(model, d.function));
    paramsFit(f, inputs, 'function', `an input of contract "${c.id}"`);
    returnsFit(model, c, f, 'function');
    const bad = errorsFit(c, fnErrors(model, f, 'function'), `Error variant of function "${f.id}"`);
    if (bad) throw new Finding('derivation.signature', `${bad}.`, ['function']);
    return;
  }

  const needs = /** @type {NonNullable<ReturnType<typeof fnOf>>} */ (fnOf(model, d.needs));
  const decide = /** @type {NonNullable<ReturnType<typeof fnOf>>} */ (fnOf(model, d.decide));
  const load = calledContract(model, c, d.load, 'load');
  const loaded = load ? typesByName(load.data.outputs) : new Map();
  for (const n of loaded.keys()) {
    if (inputs.has(n)) throw new Finding('derivation.load', `Output "${n}" of the load contract "${load?.id}" is named like an input of contract "${c.id}", so a parameter of that name would be ambiguous.`, ['load']);
  }
  const header = d.header === true;
  // With a header, the needs function reads what the header load gave; an unresolved load contract is the parser's finding.
  if (header && load) paramsFit(needs, new Map([...inputs, ...loaded]), 'needs', `an input of contract "${c.id}" or an output of its load contract "${load.id}", loaded as the header`);
  else if (!header) paramsFit(needs, inputs, 'needs', `an input of contract "${c.id}"`);
  const need = listItem(needs.returns);
  if (need === undefined) throw new Finding('derivation.signature', `Function "${needs.id}" (needs) gives ${needs.returns || 'nothing'}; it gives list<N>, the needs to load.`, ['needs']);
  const needErrs = errorsFit(c, fnErrors(model, needs, 'needs'), `Error variant of function "${needs.id}"`);
  if (needErrs) throw new Finding('derivation.signature', `${needErrs}.`, ['needs']);

  if (!load) return;
  inputsFit(c, load, inputs, { type: needs.returns, what: 'the needs' }, 'load');
  const loadErrs = errorsFit(c, list(load.data.errors).filter(isObj).map((e) => ({ name: e.name, type: e.type === undefined ? undefined : norm(e.type) })), `The error of the load contract "${load.id}"`);
  if (loadErrs) throw new Finding('derivation.load', `${loadErrs}.`, ['load']);

  const scope = new Map([...inputs, ...loaded]);
  paramsFit(decide, scope, 'decide', `an input of contract "${c.id}" or an output of its load contract "${load.id}"`);
  const decideErrs = fnErrors(model, decide, 'decide');
  const bad = errorsFit(c, decideErrs, `Error variant of function "${decide.id}"`);
  if (bad) throw new Finding('derivation.signature', `${bad}.`, ['decide']);
  if (loops) {
    const insufficient = decideErrs.find((v) => v.name === d.insufficient);
    if (!insufficient) throw new Finding('derivation.signature', `"insufficient" of contract "${c.id}" names "${d.insufficient}", which is not a variant of ${decide.errors ? `"${decide.errors.id}", the errors of function "${decide.id}"` : `the errors of function "${decide.id}", which declares none`}.`, ['insufficient']);
    if (insufficient.type !== need) throw new Finding('derivation.signature', `The insufficient-state variant "${insufficient.name}" of function "${decide.id}" carries ${insufficient.type ?? 'nothing'}; it carries one need, ${need}.`, ['insufficient']);
  }
  if (kind === 'read') {
    returnsFit(model, c, decide, 'decide');
    return;
  }

  // command

  const commit = calledContract(model, c, d.commit, 'commit');
  if (!commit) return;
  inputsFit(c, commit, scope, { type: decide.returns, what: `what decide gives` }, 'commit');
  const commitErrors = list(commit.data.errors).filter(isObj);
  if (!commitErrors.some((e) => e.name === d.conflict)) throw new Finding('derivation.commit', `"conflict" of contract "${c.id}" names "${d.conflict}", which is not an error of its commit contract "${commit.id}".`, ['conflict']);
  const commitErrs = errorsFit(c, commitErrors.map((e) => ({ name: e.name, type: e.type === undefined ? undefined : norm(e.type) })), `The error of the commit contract "${commit.id}"`);
  if (commitErrs) throw new Finding('derivation.commit', `${commitErrs}.`, ['commit']);
  const committed = typesByName(commit.data.outputs);
  const decided = typeDecl(model, decide.returns);
  const decidedFields = decided?.kind === 'struct' ? typesByName(decided.fields) : new Map();
  const outs = list(c.data.outputs).filter(isObj);
  for (const o of outs) {
    const t = fieldType(o);
    if (committed.get(o.name) === t || decidedFields.get(o.name) === t) continue;
    if (outs.length === 1 && t === decide.returns) continue;
    throw new Finding('derivation.commit', `Output "${o.name}" (${t}) of contract "${c.id}" is neither an output of its commit contract "${commit.id}" nor a field of ${decide.returns}, what function "${decide.id}" gives, of that name and type.`, ['commit']);
  }
}

/** @param {Model} model @param {Entity} c */
function checkFacade(model, c) {
  if (c.data.implementedBy !== undefined) throw new Finding('contract.facade-route', `Contract "${c.id}" is a facade, which has no server implementation, but names "${c.data.implementedBy}" in "implementedBy".`);
  const mine = routeShape(c.data.bffRoute);
  if (!mine) throw new Finding('contract.facade-route', `Facade "${c.id}" needs a bffRoute "<METHOD> <path> <shape> ..." naming the generic contract it is lowered onto; found ${c.data.bffRoute === undefined ? 'none' : JSON.stringify(c.data.bffRoute)}.`);
  const served = (model.byKind.contract ?? []).filter((o) => {
    if (o.id === c.id || o.data.realisation === 'facade' || o.data.realisation === 'target' || o.data.implementedBy === undefined) return false;
    const r = routeShape(o.data.bffRoute);
    return r !== undefined && r.method === mine.method && r.path === mine.path && r.shape === mine.shape;
  });
  if (served.length !== 1) {
    throw new Finding('contract.facade-route', served.length
      ? `Facade "${c.id}" names "${mine.method} ${mine.path} ${mine.shape}", which several served contracts state (${served.map((o) => o.id).join(', ')}); exactly one must.`
      : `Facade "${c.id}" names "${mine.method} ${mine.path} ${mine.shape}", which no served contract (not a facade, with implementedBy) states as its bffRoute.`);
  }
}

/**
 * The consistency rules of derived and facade contracts.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkDerivations(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const c of model.byKind.contract ?? []) {
    const realisation = c.data.realisation;
    const d = c.data.derivation;
    try {
      if (realisation !== 'derived' && d !== undefined) throw new Finding('derivation.kind', `Contract "${c.id}" is not derived (realisation ${JSON.stringify(realisation ?? null)}), so it takes no "derivation".`);
      if (realisation === 'derived') checkDerived(model, c, d);
      if (realisation === 'facade') checkFacade(model, c);
    } catch (e) {
      if (!(e instanceof Finding)) throw e;
      const at = e.code === 'contract.facade-route' ? [] : d === undefined ? ['realisation'] : ['derivation', ...e.at];
      out.push({ code: e.code, severity: 'error', message: e.message, entityId: c.id, loc: c.loc, path: [...c.path, ...at] });
    }
  }
  return out;
}

/**
 * Readiness of derived contracts: every function a derivation names is declared.
 * @param {Model} model @returns {Gap[]}
 */
export function derivationReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  for (const c of model.byKind.contract ?? []) {
    const d = c.data.derivation;
    if (c.data.realisation !== 'derived' || !isObj(d) || !Object.hasOwn(DERIVATION_KINDS, d.kind)) continue;
    for (const k of FUNCTION_FIELDS) {
      if (typeof d[k] !== 'string' || !d[k] || fnOf(model, d[k])) continue;
      out.push({ code: 'ready.derived-function-missing', severity: 'error', message: `The derivation of contract "${c.id}" names "${d[k]}" in "${k}", which is not a declared function.`, entityId: c.id });
    }
  }
  return out;
}

/**
 * Run a read or command derivation against a store, the way Strata's storage-api execute does (WG-4968): the
 * simulator of the load-decide-commit loop. Values are in memory (decoded: see decodeValue in function-value.js);
 * the contract's inputs are given by name. The store answers `load(needs)` with {outputs} (the load contract's
 * outputs by name) or {error: {name, value?}}, and `commit(decided, loaded)` with {outputs} or {error}.
 *
 * With a header the store is first asked for no needs; what it gives is read by the needs function, whose list is
 * then loaded in one round that does not count against needRounds. While decide fails with the insufficient variant,
 * carrying a need not yet asked for, and fewer than needRounds extra needs were asked for, the need is added and
 * everything is loaded again. A commit that fails with the conflict error is retried by deciding again, at most
 * retries times. Any other failure, and insufficient or conflict once their bound is spent, is the contract's error
 * of the same name.
 *
 * Returns {decided, outputs?, loads, rounds, conflicts}, where loads is the list of needs lists the store was asked
 * to load, in order (the header's empty list first), or {error: {name, value?}, loads, rounds, conflicts}. A function
 * that fails with a variant gives {error: {name: <words of the variant>, value}}.
 * @param {Model} model @param {string} contractId @param {Record<string, any>} inputs
 * @param {{load: (needs: any[]) => {outputs: Record<string, any>} | {error: {name: string, value?: any}}, commit?: (decided: any, loaded: Record<string, any>) => {outputs: Record<string, any>} | {error: {name: string, value?: any}}}} store
 * @returns {{decided: any, outputs?: Record<string, any>, loads: any[][], rounds: number, conflicts: number} | {error: {name: string, value?: any}, loads: any[][], rounds: number, conflicts: number}}
 */
export function runDerivation(model, contractId, inputs, store) {
  const c = model.entities.get(contractId);
  const d = c?.data.derivation;
  if (!c || c.data.realisation !== 'derived' || !isObj(d) || (d.kind !== 'read' && d.kind !== 'command')) throw new Error(`Contract "${contractId}" is not a derived read or command.`);
  const { sigs } = analyzeFunctions(model);
  /** @param {string} id */
  const sig = (id) => {
    const s = sigs.get(id);
    if (!s || !s.ok) throw new Error(`Function "${id}" of the derivation of "${contractId}" is missing or has findings.`);
    return s;
  };
  /** @param {string} id @param {Record<string, any>} scope */
  const call = (id, scope) => {
    const s = sig(id);
    return runFunction(model, s, sigs, s.params.map((p) => scope[p.name] ?? null));
  };
  /** @param {any} variant a UnionValue the function failed with */
  const asError = (variant) => ({ name: wordsOf(variant.variant), value: Object.values(variant.fields)[0] });
  const loads = /** @type {any[][]} */ ([]);
  let rounds = 0, conflicts = 0;
  /** @param {{name: string, value?: any}} error */
  const failed = (error) => ({ error, loads, rounds, conflicts });
  for (;;) {
    /** @type {Record<string, any>} */
    let header = {};
    if (d.header === true) {
      loads.push([]);
      const h = store.load([]);
      if ('error' in h) return failed(h.error);
      header = h.outputs;
    }
    const n = call(d.needs, { ...header, ...inputs });
    if ('error' in n) return failed(asError(n.error));
    const needs = [...n.value];
    rounds = 0;
    /** @type {Record<string, any>} */
    let loaded;
    /** @type {any} */
    let decided;
    for (;;) {
      loads.push([...needs]);
      const l = store.load(needs);
      if ('error' in l) return failed(l.error);
      loaded = l.outputs;
      const r = call(d.decide, { ...inputs, ...loaded });
      if ('value' in r) { decided = r.value; break; }
      const e = asError(r.error);
      if (d.insufficient !== undefined && wordsOf(d.insufficient) === e.name && rounds < d.needRounds && !needs.some((x) => valueEq(x, e.value))) {
        needs.push(e.value);
        rounds++;
        continue;
      }
      return failed(e);
    }
    if (d.kind === 'read') return { decided, loads, rounds, conflicts };
    const committed = store.commit ? store.commit(decided, loaded) : { outputs: {} };
    if ('error' in committed) {
      if (committed.error.name === wordsOf(d.conflict) && conflicts < d.retries) { conflicts++; continue; }
      return failed(committed.error);
    }
    return { decided, outputs: committed.outputs, loads, rounds, conflicts };
  }
}
