// User interface constructs: what a specification says about its pages and its user journeys, precisely
// enough to generate the frontend kernel (state, messages, effects, routes, transitions) wired to the
// backend's contracts, and end-to-end browser tests. screen (a route, the contract whose response is its
// view model, the renderer that draws it), form (fields that fill a contract's inputs), action (a button
// that calls a contract), liveBinding (an event that refreshes an open screen) and uiScenario (a user
// journey whose steps select elements by role and accessible name only). This module holds their
// consistency rules (errors, always on) and their readiness rules (codes ready.*, errors only when the
// specification sets system.generation; see readiness.js). Pure and deterministic.
// docs/model-and-format.md, "User interface".

import { parseExpr, exprRefs } from './expr.js';
import { typeClass, exprClass, typeResolves } from './codegen-model.js';
import { checkJourney, itemPlaceholders } from './ui-steps.js';
import { suppliedInputs } from './supplied-inputs.js';

export { STEP_KINDS, ARIA_ROLES } from './ui-steps.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {import('./codegen-model.js').TypeClass} TypeClass */
/** @typedef {{code: string, severity: 'error', message: string, entityId: string}} Gap */

/** The entity kinds of the user interface. */
export const UI_KINDS = Object.freeze(['screen', 'form', 'action', 'liveBinding', 'errorMessage', 'uiScenario']);

/** The class of value each control edits; a date may be held as a string or a number. */
/** @type {Record<string, TypeClass[]>} */
const CONTROL_CLASSES = { text: ['string'], textarea: ['string'], password: ['string'], select: ['string'], radio: ['string'], checkbox: ['bool'], number: ['number'], date: ['string', 'number'] };

/** Controls that offer a choice among options (listed, or taken from the view model). */
const CHOICE_CONTROLS = ['select', 'radio'];

/** Transforms a derived form field may apply to its derived value. */
const DERIVE_TRANSFORMS = ['slug'];

/** The attributes of the principal an expression may read, and their classes. */
const PRINCIPAL = new Map(/** @type {[string, TypeClass][]} */ ([['id', 'string'], ['tenant', 'string'], ['role', 'string']]));

const SEGMENT_RE = /^(?:[A-Za-z0-9._~-]+|:([a-z][A-Za-z0-9_]*))$/;
const NAME_RE = /^[a-z][A-Za-z0-9_]*$/;
/** A catch-all route: "*", or "*name" binding the unmatched path to route parameter name. */
const CATCH_ALL_RE = /^\*([a-z][A-Za-z0-9_]*)?$/;
/** A screen-local name: what expressions read as local.<name> (inner hyphens allowed, as in entity ids). */
const LOCAL_NAME_RE = /^[a-z][A-Za-z0-9_]*(?:-[A-Za-z0-9_]+)*$/;
/** A placeholder of a toast: ${scope.name} or ${scope.name.field...}. */
const PLACEHOLDER_RE = /\$\{([^}]*)\}/g;
const PLACEHOLDER_PATH_RE = /^[A-Za-z_][A-Za-z0-9_]*(?:-[A-Za-z0-9_]+)*(?:\.[A-Za-z_][A-Za-z0-9_]*(?:-[A-Za-z0-9_]+)*)+$/;
const AUTH_RE = /^(?:none|session|role:[A-Za-z0-9_.-]+)$/;
const WRAPPER_RE = /^(list|option|set|shared)<(.+)>$/;
/** The controls whose value is a text a person types. */
const TYPED_CONTROLS = ['text', 'textarea', 'password'];
/** A check kind or error code an error message words. */
const KIND_RE = /^[a-z][a-z0-9_-]*$/;
/** The placeholders of an error message, by what it words. */
const MESSAGE_PLACEHOLDERS = { check: ['check.detail', 'check.statement'], error: ['error.message'] };
/** The scopes an action offered on other screens too (alsoOn) may not read. */
const SCREEN_SCOPES = ['route', 'query', 'view', 'local', 'item', 'form'];

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v */
const nonEmpty = (v) => typeof v === 'string' && v.trim() !== '';

/**
 * The parameter names of a route pattern, or an error message when the pattern is not well formed: "/" or
 * one or more "/segment", each a literal of URL-safe characters or ":name", with no parameter twice; or a
 * catch-all, "*" or "*name", which answers every path no other screen answers (name: the parameter that
 * holds that path).
 * @param {any} route @returns {{params: string[], catchAll?: true, error?: string}}
 */
export function routeParams(route) {
  if (typeof route !== 'string') return { params: [], error: 'it is not a string' };
  if (route === '/') return { params: [] };
  if (route.startsWith('*')) {
    const m = CATCH_ALL_RE.exec(route);
    return m ? { params: m[1] ? [m[1]] : [], catchAll: true } : { params: [], catchAll: true, error: 'a catch-all route is "*" or "*name"' };
  }
  /** @type {string[]} */
  const params = [];
  /** @type {string|undefined} */
  let error;
  if (!route.startsWith('/') || route.endsWith('/')) error = 'it must start with "/" and, unless it is "/", not end with one';
  // Every parameter is collected even past an error, so the rules that read a screen's parameters do not
  // report a second error for one malformed route.
  for (const seg of route.replace(/^\/|\/$/g, '').split('/')) {
    const m = SEGMENT_RE.exec(seg);
    if (!m) { error ??= `segment "${seg}" is neither a literal (letters, digits, . _ ~ -) nor ":name"`; continue; }
    if (m[1] === undefined) continue;
    if (params.includes(m[1])) error ??= `parameter "${m[1]}" appears twice`;
    else params.push(m[1]);
  }
  return error === undefined ? { params } : { params, error };
}

/** The shape of a route, parameters made anonymous, so /posts/:slug and /posts/:id are one route. @param {string} route */
const routeShape = (route) => route.split('/').map((s) => (s.startsWith(':') ? ':' : s)).join('/');

/** The fields of a value nothing is known about: every name is one, of unknown class. */
class AnyFields extends Map {
  /** @param {any} _k */
  has(_k) { return true; }
  /** @param {any} _k @returns {TypeClass} */
  get(_k) { return 'any'; }
}

/**
 * Named, typed fields (contract inputs or outputs) as a map from name to the field.
 * @param {any} fields @returns {Map<string, any>}
 */
const fieldMap = (fields) => new Map(list(fields).filter((f) => isObj(f) && typeof f.name === 'string').map((f) => [f.name, f]));

/**
 * The consistency rules of the user interface constructs.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkUiConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  /** @param {any} id @param {string} k @returns {Entity|undefined} */
  const get = (id, k) => {
    const e = typeof id === 'string' ? model.entities.get(id) : undefined;
    return e && e.kind === k ? e : undefined;
  };
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];
  /** @param {any} fields @returns {Map<string, TypeClass>} */
  const classes = (fields) => new Map([...fieldMap(fields)].map(([n, f]) => [n, typeClass(model, f.type)]));

  /**
   * An expression: it parses, every reference is in scope, and the judge accepts its class.
   * @param {Entity} e @param {any} src @param {(string|number)[]} sub
   * @param {Map<string, Map<string, TypeClass>>} scope @param {(cls: TypeClass) => string|undefined} judge
   */
  const checkExpr = (e, src, sub, scope, judge) => {
    if (typeof src !== 'string') { err(`${e.kind}.expr-syntax`, e, `Expected an expression (a string), found ${JSON.stringify(src)}.`, sub); return; }
    const parsed = parseExpr(src);
    if (!parsed.ok) { err(`${e.kind}.expr-syntax`, e, `Expression "${src}": ${parsed.error.message} (at character ${parsed.error.pos + 1}).`, sub); return; }
    let bad = false;
    for (const path of exprRefs(parsed.ast)) {
      if (path.length === 2 && scope.get(path[0])?.has(path[1])) continue;
      bad = true;
      err(`${e.kind}.expr-reference`, e, `Expression "${src}": "${path.join('.')}" is not in scope here (in scope: ${[...scope.keys()].join(', ')}, each with its declared fields).`, sub);
    }
    if (bad) return;
    const r = exprClass(parsed.ast, (path) => scope.get(path[0])?.get(path[1]) ?? 'any');
    const complaint = r.error ?? judge(r.cls);
    if (complaint) err(`${e.kind}.expr-type`, e, `Expression "${src}": ${complaint}.`, sub);
  };

  // --- request encoding ----------------------------------------------------------
  // encode on a contract input: how a page's request turns the value it holds into what the endpoint takes.
  for (const c of kind('contract')) {
    list(c.data.inputs).forEach((inp, i) => {
      if (!isObj(inp) || inp.encode === undefined) return;
      const enc = inp.encode;
      const at = ['inputs', i, 'encode'];
      /** @param {string} why @param {(string|number)[]} [where] */
      const bad = (why, where = at) => err('contract.encode', c, `Input "${inp.name}" of contract "${c.id}" is encoded: ${why}.`, where);
      if (!isObj(enc)) { bad('"encode" is {trim?, split?, as?, empty?}'); return; }
      const extra = Object.keys(enc).filter((k) => !['trim', 'split', 'as', 'empty'].includes(k));
      if (extra.length) { bad(`${extra.join(', ')} ${extra.length > 1 ? 'are' : 'is'} not part of "encode" (trim, split, as, empty)`); return; }
      if (!Object.keys(enc).length) { bad('it says nothing (trim, split, as or empty)'); return; }
      const cls = typeClass(model, inp.type);
      const reads = ['trim', 'split', 'as'].filter((k) => enc[k] !== undefined);
      if (reads.length && cls !== 'string' && cls !== 'any') bad(`${reads.join(', ')} ${reads.length > 1 ? 'read' : 'reads'} a text, but the input is a ${cls}`, [...at, reads[0]]);
      if (enc.split !== undefined && !(typeof enc.split === 'string' && enc.split !== '')) bad('split names a separator, a text that is not empty', [...at, 'split']);
      if (enc.split !== undefined && enc.as !== undefined) bad('a text split into a list is not also made a number; split and as exclude each other', [...at, 'as']);
      if (enc.empty !== undefined && inp.optional !== true) bad(`an empty value is ${enc.empty === 'omit' ? 'left out' : 'sent as null'}, which only an optional input allows`, [...at, 'empty']);
    });
  }

  // --- screens ----------------------------------------------------------------
  /** @type {Map<string, {params: string[], query: string[], catchAll: boolean}>} */
  const screenParams = new Map();
  /** The screen-local state each screen declares: name -> type. @type {Map<string, Map<string, any>>} */
  const screenLocals = new Map();
  /** @type {Map<string, string>} */
  const shapes = new Map();
  /** @type {string|undefined} */
  let catchAllScreen;
  for (const s of kind('screen')) {
    const d = s.data;
    const { params, catchAll, error } = routeParams(d.route);
    if (error) err('screen.route', s, `Route ${JSON.stringify(d.route)} of screen "${s.id}" is not a path pattern: ${error}.`, ['route']);
    const query = list(d.query).filter((q) => typeof q === 'string');
    list(d.query).forEach((q, i) => {
      if (typeof q !== 'string' || !NAME_RE.test(q)) err('screen.route', s, `Query parameter ${JSON.stringify(q)} of screen "${s.id}" is not a name (a lower-case letter, then letters, digits or _).`, ['query', i]);
      else if (params.includes(q) || query.indexOf(q) !== i) err('screen.route', s, `Parameter "${q}" of screen "${s.id}" is named twice.`, ['query', i]);
    });
    screenParams.set(s.id, { params, query, catchAll: catchAll === true });
    if (catchAll) {
      if (catchAllScreen) err('screen.catch-all-duplicate', s, `Screen "${s.id}" is a second catch-all screen; screen "${catchAllScreen}" already answers every path no other screen answers.`, ['route']);
      else catchAllScreen = s.id;
    } else if (!error) {
      const shape = routeShape(d.route);
      const first = shapes.get(shape);
      if (first) err('screen.route-duplicate', s, `Screen "${s.id}" answers the same route as screen "${first}" (${d.route}).`, ['route']);
      else shapes.set(shape, s.id);
    }
    /** @type {Map<string, any>} */
    const locals = new Map();
    list(d.local).forEach((l, i) => {
      const at = ['local', i];
      if (!isObj(l) || typeof l.name !== 'string' || !LOCAL_NAME_RE.test(l.name)) { err('screen.local', s, `Screen-local value ${i + 1} of screen "${s.id}" needs a "name" (a lower-case letter, then letters, digits, _ or inner hyphens).`, at); return; }
      if (locals.has(l.name)) { err('screen.local', s, `Screen "${s.id}" declares screen-local value "${l.name}" twice.`, [...at, 'name']); return; }
      if (typeof l.type !== 'string' || !typeResolves(model, l.type)) err('screen.local', s, `Screen-local value "${l.name}" of screen "${s.id}" has type ${JSON.stringify(l.type)}, which is neither built-in nor a declared type.`, [...at, 'type']);
      locals.set(l.name, l.type);
    });
    screenLocals.set(s.id, locals);
    if (d.auth !== undefined && !(typeof d.auth === 'string' && AUTH_RE.test(d.auth))) err('screen.auth', s, `Authentication ${JSON.stringify(d.auth)} of screen "${s.id}" is not none, session or role:<role>.`, ['auth']);
    if (d.kind !== undefined && !nonEmpty(d.kind)) err('screen.kind', s, `The renderer of screen "${s.id}" is empty.`, ['kind']);
    const vm = get(d.viewModel, 'contract');
    if (vm && !error) {
      for (const [name, f] of fieldMap(vm.data.inputs)) {
        if (f.optional !== true && !params.includes(name) && !query.includes(name)) err('screen.view-model-input', s, `View-model contract "${vm.id}" needs input "${name}", which is not a parameter of route ${d.route}${query.length ? ` or its query` : ''}.`, ['viewModel']);
      }
    }
  }
  // Two screens whose routes tie (WG-4955): the condition the generator refuses, as its refuse_route_ties does.
  // Both routes are non-catch-all, have the same number of segments, agree at every position (equal literals,
  // or a parameter on either side) and have the same number of literal segments. Routes of one shape are
  // screen.route-duplicate, reported above, so they are not reported again here.
  const routed = kind('screen')
    .filter((s) => !routeParams(s.data.route).error && !s.data.route.startsWith('*'))
    .map((s) => ({ s, shape: routeShape(s.data.route), segs: s.data.route === '/' ? [] : s.data.route.slice(1).split('/') }));
  const literalCount = (/** @type {string[]} */ segs) => segs.filter((p) => !p.startsWith(':')).length;
  routed.forEach((b, j) => routed.slice(0, j).forEach((a) => {
    const tie = a.shape !== b.shape && a.segs.length === b.segs.length
      && a.segs.every((p, k) => p.startsWith(':') || b.segs[k].startsWith(':') || p === b.segs[k])
      && literalCount(a.segs) === literalCount(b.segs);
    if (tie) err('route.ambiguous', b.s, `Screens "${a.s.id}" and "${b.s.id}" have routes that answer the same path (${a.s.data.route} and ${b.s.data.route}) with the same number of literal segments, so which one opens would depend on the order they are declared in.`, ['route']);
  }));

  /**
   * What an expression on a screen may read: its route and query parameters (route.<name>, strings), its
   * query parameters alone (query.<name>), the outputs of its view-model contract, its screen-local values
   * (local.<name>) and the principal.
   * @param {Entity|undefined} screen @returns {Map<string, Map<string, TypeClass>>}
   */
  const screenScope = (screen) => {
    const p = screen ? screenParams.get(screen.id) : undefined;
    const str = (/** @type {string} */ n) => /** @type {[string, TypeClass]} */ ([n, 'string']);
    /** @type {Map<string, Map<string, TypeClass>>} */
    const scope = new Map([['route', new Map([...(p?.params ?? []), ...(p?.query ?? [])].map(str))], ['query', new Map((p?.query ?? []).map(str))]]);
    const vm = screen ? get(screen.data.viewModel, 'contract') : undefined;
    scope.set('view', vm ? classes(vm.data.outputs) : new Map());
    scope.set('local', new Map([...(screen ? screenLocals.get(screen.id) ?? new Map() : new Map())].map(([n, t]) => [n, typeClass(model, t)])));
    scope.set('principal', PRINCIPAL);
    return scope;
  };

  /**
   * A toast: a text whose placeholders ${scope.name} (and, for response and view, ${scope.output.field...}
   * through struct fields) read names in scope, each a value that can be shown as text.
   * @param {Entity} e @param {Map<string, Map<string, TypeClass>>} scope @param {Entity|undefined} contract @param {Entity|undefined} screen
   */
  const checkToast = (e, scope, contract, screen) => {
    const text = isObj(e.data.onSuccess) ? e.data.onSuccess.toast : undefined;
    if (typeof text !== 'string') return;
    const vm = screen ? get(screen.data.viewModel, 'contract') : undefined;
    for (const m of text.matchAll(PLACEHOLDER_RE)) {
      /** @param {string} why */
      const bad = (why) => err(`${e.kind}.toast-template`, e, `The toast of ${e.kind} "${e.id}" has placeholder "${m[0]}": ${why}.`, ['onSuccess', 'toast']);
      if (!PLACEHOLDER_PATH_RE.test(m[1])) { bad(`a placeholder is \${<scope>.<name>}, a scope one of ${[...scope.keys()].join(', ')}`); continue; }
      const [head, ...rest] = m[1].split('.');
      const fields = scope.get(head);
      if (!fields) { bad(`"${head}" is not in scope here (in scope: ${[...scope.keys()].join(', ')})`); continue; }
      const over = head === 'response' ? contract : head === 'view' ? vm : undefined;
      /** @type {TypeClass} */
      let cls;
      if (over) {
        const r = viewPathType(model, over, rest.join('.'));
        if (r.error) { bad(r.error); continue; }
        cls = typeClass(model, r.type);
      } else {
        if (rest.length !== 1 || !fields.has(rest[0])) { bad(`"${rest.join('.')}" is not a name of ${head} here`); continue; }
        cls = /** @type {TypeClass} */ (fields.get(rest[0]));
      }
      if (cls === 'list' || cls === 'struct' || cls === 'bytes' || cls === 'json') bad(`it is a ${cls}, which a toast cannot show as text`);
    }
  };

  /**
   * Arguments: input -> expression, every key an input of the contract, each of that input's class.
   * @param {Entity} e @param {any} args @param {Entity|undefined} contract @param {Map<string, Map<string, TypeClass>>} scope
   * @param {(string|number)[]} [at] Where the arguments are, in the entity.
   */
  const checkArguments = (e, args, contract, scope, at = ['arguments']) => {
    if (!isObj(args) || !contract) return;
    const inputs = fieldMap(contract.data.inputs);
    const supplied = suppliedInputs(contract);
    for (const [name, src] of Object.entries(args)) {
      const f = inputs.get(name);
      if (!f) { err(`${e.kind}.argument-unknown`, e, `Contract "${contract.id}" has no input "${name}".`, [...at, name]); continue; }
      if (supplied.has(name)) { err(`${e.kind}.supplied-input`, e, `Input "${name}" of contract "${contract.id}" is supplied by its ${supplied.get(name)}, never by the body, so ${e.kind} "${e.id}" cannot give it.`, [...at, name]); continue; }
      const want = typeClass(model, f.type);
      checkExpr(e, src, [...at, name], scope, (cls) => (
        cls === want || cls === 'any' || want === 'any' || (cls === 'null' && f.optional === true) ? undefined : `it is a ${cls}, but input "${name}" of contract "${contract.id}" is a ${want}`));
    }
  };

  /**
   * What the outcome of a call (onSuccess: navigate, toast) may read: the screen's scope, response.<output>
   * of the call, and for a form form.<field> (the submitted value of each field, of its input's class).
   * @param {Map<string, Map<string, TypeClass>>} scope @param {Entity|undefined} contract @param {Map<string, TypeClass>} [form]
   */
  const outcomeScope = (scope, contract, form) => {
    const out = new Map(scope);
    out.set('response', contract ? classes(contract.data.outputs) : new Map());
    if (form) out.set('form', form);
    return out;
  };

  /**
   * onSuccess.navigate: the target screen's route parameters are given exactly (query parameters may be),
   * each by an expression of a string or a number over the outcome scope. A catch-all screen has no address
   * of its own, so nothing navigates to it. `path`, when given, is an expression of a string: the address to
   * open when it is a same-site absolute path (it starts with "/" and not "//"); the screen is the fallback.
   * @param {Entity} e @param {Map<string, Map<string, TypeClass>>} navScope
   */
  const checkNavigate = (e, navScope) => {
    const nav = isObj(e.data.onSuccess) ? e.data.onSuccess.navigate : undefined;
    if (!isObj(nav)) return;
    const sub = ['onSuccess', 'navigate'];
    if (nav.path !== undefined) checkExpr(e, nav.path, [...sub, 'path'], navScope, (cls) => (cls === 'string' || cls === 'any' || cls === 'null' ? undefined : `it is a ${cls}, and an address is a string`));
    const target = get(nav.screen, 'screen');
    if (!target) return;
    const p = screenParams.get(target.id) ?? { params: [], query: [], catchAll: false };
    if (p.catchAll) { err(`${e.kind}.navigate-params`, e, `Screen "${target.id}" is the catch-all screen; it has no address of its own, so nothing navigates to it.`, [...sub, 'screen']); return; }
    const given = isObj(nav.params) ? nav.params : {};
    const missing = p.params.filter((n) => !Object.hasOwn(given, n));
    const extra = Object.keys(given).filter((n) => !p.params.includes(n) && !p.query.includes(n));
    if (missing.length || extra.length) err(`${e.kind}.navigate-params`, e, `Navigating to screen "${target.id}" (${target.data.route}) must give its route parameters${p.params.length ? ` (${p.params.join(', ')})` : ' (none)'}${missing.length ? `; missing ${missing.join(', ')}` : ''}${extra.length ? `; not parameters of it: ${extra.join(', ')}` : ''}.`, [...sub, 'params']);
    for (const [name, src] of Object.entries(given)) {
      if (extra.includes(name)) continue;
      checkExpr(e, src, [...sub, 'params', name], navScope, (cls) => (cls === 'string' || cls === 'number' || cls === 'any' ? undefined : `it is a ${cls}, and a route parameter is a string or a number`));
    }
  };

  /**
   * onSuccess.view: outputs of the view model of the screen the success opens (navigate.screen, else the
   * entity's own screen) that hold these values until that view model is read again; each an expression over
   * the outcome scope of the output's class.
   * @param {Entity} e @param {Map<string, Map<string, TypeClass>>} navScope @param {Entity|undefined} screen
   */
  const checkViewOverlay = (e, navScope, screen) => {
    const ov = isObj(e.data.onSuccess) ? e.data.onSuccess.view : undefined;
    if (ov === undefined) return;
    const at = ['onSuccess', 'view'];
    if (!isObj(ov)) { err(`${e.kind}.view-overlay`, e, `The view-model values the success of ${e.kind} "${e.id}" sets are output -> expression.`, at); return; }
    const nav = isObj(e.data.onSuccess.navigate) ? e.data.onSuccess.navigate : undefined;
    const target = nav ? get(nav.screen, 'screen') : screen;
    if (!target) return;
    const vm = get(target.data.viewModel, 'contract');
    if (!vm) { err(`${e.kind}.view-overlay`, e, `The success of ${e.kind} "${e.id}" sets values of the view model of screen "${target.id}", which names no view-model contract.`, at); return; }
    const outs = fieldMap(vm.data.outputs);
    for (const [name, src] of Object.entries(ov)) {
      const out = outs.get(name);
      if (!out) { err(`${e.kind}.view-overlay`, e, `The success of ${e.kind} "${e.id}" sets "${name}", which is not an output of view-model contract "${vm.id}" of screen "${target.id}".`, [...at, name]); continue; }
      const want = typeClass(model, out.type);
      checkExpr(e, src, [...at, name], navScope, (cls) => (cls === want || cls === 'any' || want === 'any' || (cls === 'null' && out.optional === true) ? undefined : `it is a ${cls}, but output "${name}" of "${vm.id}" is a ${want}`));
    }
  };

  /**
   * onError.prefix and onError.announce: texts, not empty.
   * @param {Entity} e
   */
  const checkOnError = (e) => {
    const oe = e.data.onError;
    if (!isObj(oe)) return;
    for (const k of ['prefix', 'announce']) {
      if (oe[k] !== undefined && !nonEmpty(oe[k])) err(`${e.kind}.on-error`, e, `The ${k} of the refusal of ${e.kind} "${e.id}" is empty; leave it out instead.`, ['onError', k]);
    }
  };

  /**
   * initial of a form field: {path, join?} reaches a value in the screen's view model of the control's class
   * (a number for a control that edits a text, a list of texts with join); {path, where: {field, equals},
   * value} reaches a list of structs and takes value of the first item whose field equals the expression.
   * @param {Entity} f @param {any} fld @param {(string|number)[]} sub @param {Entity|undefined} screen
   * @param {Map<string, Map<string, TypeClass>>} scope
   */
  const checkInitial = (f, fld, sub, screen, scope) => {
    const ini = fld.initial;
    const at = [...sub, 'initial'];
    /** @param {string} code @param {string} why @param {(string|number)[]} [where] */
    const bad = (code, why, where = at) => err(code, f, `Field "${fld.name}" of form "${f.id}" takes its initial value from the view model: ${why}.`, where);
    if (!isObj(ini) || typeof ini.path !== 'string') { bad('form.initial', '"initial" is {path, where?, value?, join?}, path a path into the view model'); return; }
    const extra = Object.keys(ini).filter((k) => !['path', 'where', 'value', 'join'].includes(k));
    if (extra.length) { bad('form.initial', `${extra.join(', ')} ${extra.length > 1 ? 'are' : 'is'} not part of "initial" (path, where, value, join)`); return; }
    const vm = screen ? get(screen.data.viewModel, 'contract') : undefined;
    if (!vm) { if (screen) bad('form.initial', `screen "${screen.id}" names no view-model contract`, [...at, 'path']); return; }
    const fits = CONTROL_CLASSES[fld.control] ?? ['string'];
    const text = fits.includes('string');
    /** Whether a value of this class can fill the control: its own class, or a number shown as text. @param {TypeClass} cls */
    const fills = (cls) => cls === 'any' || fits.includes(cls) || (text && cls === 'number');
    const r = viewPathType(model, vm, ini.path);
    if (r.error) { bad(ini.where === undefined ? 'form.initial' : 'form.initial-where', r.error, [...at, 'path']); return; }
    if (r.type === undefined) return;
    const reached = typeof r.type === 'string' ? r.type.trim() : '';
    const m = /^list<(.+)>$/.exec(reached);
    if (ini.where === undefined) {
      if (ini.value !== undefined) bad('form.initial-where', '"value" picks a path in the item "where" finds, so it needs "where"', [...at, 'value']);
      if (ini.join !== undefined) {
        const itemCls = m ? typeClass(model, m[1].trim()) : undefined;
        if (!(typeof ini.join === 'string' && text && (itemCls === 'string' || itemCls === 'any'))) bad('form.initial', `join turns a list of texts into the text of a control that edits one, but "${ini.path}" reaches "${reached}" and the control is a ${fld.control}`, [...at, 'join']);
        return;
      }
      const cls = typeClass(model, reached);
      if (!fills(cls)) bad('form.initial', `"${ini.path}" reaches a ${cls}, but a ${fld.control} control edits a ${fits.join(' or a ')}`, [...at, 'path']);
      return;
    }
    // where: the first item of a list of structs whose field equals the expression.
    const w = ini.where;
    if (ini.join !== undefined) bad('form.initial-where', 'join applies to a list of texts, not to the value of a found item', [...at, 'join']);
    const el = m ? model.entities.get(m[1].trim()) : undefined;
    if (!m || el?.kind !== 'type' || el.data.kind !== 'struct') { bad('form.initial-where', `"where" finds an item of a list of structs, but "${ini.path}" reaches "${reached}"`, [...at, 'path']); return; }
    if (!isObj(w) || typeof w.field !== 'string' || typeof w.equals !== 'string' || Object.keys(w).some((k) => k !== 'field' && k !== 'equals')) { bad('form.initial-where', '"where" is {field, equals}: a path in the item and an expression', [...at, 'where']); return; }
    const wf = typePathType(model, el.id, w.field.split('.'));
    if (wf.error) bad('form.initial-where', wf.error, [...at, 'where', 'field']);
    else {
      const want = wf.type === undefined ? 'any' : typeClass(model, wf.type);
      checkExpr(f, w.equals, [...at, 'where', 'equals'], scope, (cls) => (cls === want || cls === 'any' || want === 'any' ? undefined : `it is a ${cls}, but "${w.field}" of the items is a ${want}`));
    }
    if (typeof ini.value !== 'string') { bad('form.initial-where', '"value" names the path in the found item that gives the value', at); return; }
    const vf = typePathType(model, el.id, ini.value.split('.'));
    if (vf.error) { bad('form.initial-where', vf.error, [...at, 'value']); return; }
    if (vf.type !== undefined && !fills(typeClass(model, vf.type))) bad('form.initial-where', `"${ini.value}" of the items is a ${typeClass(model, vf.type)}, but a ${fld.control} control edits a ${fits.join(' or a ')}`, [...at, 'value']);
  };

  /**
   * optionsFrom of a select or radio field: {path, value?, label?}. path reaches a list in the screen's view
   * model; for a list of a declared struct, value and label name its fields (value of the control's class,
   * label a string); for a list of strings (or enum values) each item is its own value and label.
   * @param {Entity} f @param {any} fld @param {(string|number)[]} sub @param {Entity|undefined} screen
   */
  const checkOptionsFrom = (f, fld, sub, screen) => {
    const of = fld.optionsFrom;
    const at = [...sub, 'optionsFrom'];
    /** @param {string} why @param {(string|number)[]} [where] */
    const bad = (why, where = at) => err('form.options-from', f, `Field "${fld.name}" of form "${f.id}" takes its options from the view model: ${why}.`, where);
    if (!isObj(of) || typeof of.path !== 'string') { bad('"optionsFrom" is {path, value?, label?}, path a path into the view model'); return; }
    const extra = Object.keys(of).filter((k) => !['path', 'value', 'label'].includes(k));
    if (extra.length) { bad(`${extra.join(', ')} ${extra.length > 1 ? 'are' : 'is'} not part of "optionsFrom" (path, value, label)`); return; }
    const vm = screen ? get(screen.data.viewModel, 'contract') : undefined;
    if (!vm) { if (screen) bad(`screen "${screen.id}" names no view-model contract`, [...at, 'path']); return; }
    const r = viewPathType(model, vm, of.path);
    if (r.error) { bad(r.error, [...at, 'path']); return; }
    if (r.type === undefined) return;
    const text = typeof r.type === 'string' ? r.type.trim() : '';
    const m = /^list<(.+)>$/.exec(text);
    if (!m) { bad(`"${of.path}" reaches a value of type "${text}", not a list`, [...at, 'path']); return; }
    const el = model.entities.get(m[1].trim());
    const fits = CONTROL_CLASSES[fld.control] ?? ['string'];
    if (el?.kind === 'type' && el.data.kind === 'struct') {
      const fields = classes(el.data.fields);
      for (const k of /** @type {const} */ (['value', 'label'])) {
        if (typeof of[k] !== 'string') { bad(`its items are struct "${el.id}", so "${k}" names the field that gives each option's ${k}`, at); continue; }
        const cls = fields.get(of[k]);
        if (cls === undefined) bad(`struct "${el.id}" has no field "${of[k]}"`, [...at, k]);
        else if (cls !== 'any' && !(k === 'label' ? cls === 'string' : fits.includes(cls))) bad(`field "${of[k]}" of struct "${el.id}" is a ${cls}, but ${k === 'label' ? 'a label is a string' : `a ${fld.control} control edits a ${fits.join(' or a ')}`}`, [...at, k]);
      }
      return;
    }
    const cls = typeClass(model, m[1].trim());
    if (cls !== 'any' && !fits.includes(cls)) { bad(`its items are of type "${m[1].trim()}", but a ${fld.control} control edits a ${fits.join(' or a ')}`, [...at, 'path']); return; }
    for (const k of ['value', 'label']) if (of[k] !== undefined) bad(`its items are not structs, so each item is its own value and label and "${k}" does not apply`, [...at, k]);
  };

  /**
   * derive of a form field: an expression over the other fields (form.<field>) and the screen's scope that
   * fills the field, of its input's class (a string when transform is "slug"); until: "edited" stops deriving
   * once the field has been edited; transform names a transform applied to the derived value.
   * @param {Entity} f @param {any} fld @param {(string|number)[]} sub
   * @param {Map<string, Map<string, TypeClass>>} scope @param {Map<string, TypeClass>} formFields
   */
  const checkDerive = (f, fld, sub, scope, formFields) => {
    if (fld.derive === undefined) {
      for (const k of ['until', 'transform']) if (fld[k] !== undefined) err('form.derive', f, `Field "${fld.name}" of form "${f.id}" has "${k}" but no "derive"; it applies to a derived field only.`, [...sub, k]);
      return;
    }
    if (fld.until !== undefined && fld.until !== 'edited') err('form.derive', f, `Field "${fld.name}" of form "${f.id}" derives "until" ${JSON.stringify(fld.until)}; the only value is "edited" (left out: always derived).`, [...sub, 'until']);
    const slug = fld.transform === 'slug';
    if (fld.transform !== undefined && !DERIVE_TRANSFORMS.includes(fld.transform)) err('form.derive', f, `Field "${fld.name}" of form "${f.id}" names transform ${JSON.stringify(fld.transform)}; the transforms are ${DERIVE_TRANSFORMS.join(', ')}.`, [...sub, 'transform']);
    const own = formFields.get(fld.name) ?? 'any';
    if (slug && own !== 'string' && own !== 'any') err('form.derive', f, `Field "${fld.name}" of form "${f.id}" applies transform "slug", which yields a string, but the field's input is a ${own}.`, [...sub, 'transform']);
    const others = new Map([...formFields].filter(([n]) => n !== fld.name));
    const dscope = new Map(scope);
    dscope.set('form', others);
    const want = slug ? 'string' : own;
    checkExpr(f, fld.derive, [...sub, 'derive'], dscope, (cls) => (cls === want || cls === 'any' || want === 'any' ? undefined : `it is a ${cls}, but ${slug ? 'transform "slug" takes a string' : `field "${fld.name}" holds a ${want}`}`));
  };

  /**
   * Derived fields of a form do not derive from one another in a cycle (a field reading itself is already
   * outside its own scope).
   * @param {Entity} f
   */
  const checkDeriveCycles = (f) => {
    /** @type {Map<string, string[]>} */
    const reads = new Map();
    for (const fld of list(f.data.fields)) {
      if (!isObj(fld) || typeof fld.name !== 'string' || typeof fld.derive !== 'string') continue;
      const p = parseExpr(fld.derive);
      if (p.ok) reads.set(fld.name, exprRefs(p.ast).filter((r) => r.length === 2 && r[0] === 'form' && r[1] !== fld.name).map((r) => r[1]));
    }
    /** @type {Set<string>} */
    const done = new Set();
    for (const start of reads.keys()) {
      /** @type {string[]} */
      const pathTo = [];
      /** @param {string} n @returns {string[]|undefined} */
      const visit = (n) => {
        if (pathTo.includes(n)) return [...pathTo.slice(pathTo.indexOf(n)), n];
        if (done.has(n) || !reads.has(n)) return undefined;
        pathTo.push(n);
        for (const m of reads.get(n) ?? []) { const c = visit(m); if (c) return c; }
        pathTo.pop();
        done.add(n);
        return undefined;
      };
      const cycle = visit(start);
      if (cycle) {
        const i = list(f.data.fields).findIndex((x) => isObj(x) && x.name === cycle[0]);
        err('form.derive', f, `Fields of form "${f.id}" derive from one another in a cycle: ${cycle.join(' -> ')}.`, ['fields', i, 'derive']);
        return;
      }
    }
  };

  // --- forms ------------------------------------------------------------------
  for (const f of kind('form')) {
    const d = f.data;
    const contract = get(d.contract, 'contract');
    const inputs = contract ? fieldMap(contract.data.inputs) : undefined;
    const screen = get(d.screen, 'screen');
    const scope = screenScope(screen);
    /** @type {Set<string>} */
    const names = new Set();
    /** @type {Set<string>} */
    const filled = new Set();
    // The value of each field (form.<field>), of its input's class; a field whose input is unknown is of
    // unknown class, so one wrong input is one error.
    /** @type {Map<string, TypeClass>} */
    const formFields = new Map();
    for (const fld of list(d.fields)) {
      if (!isObj(fld) || typeof fld.name !== 'string') continue;
      const input = typeof fld.input === 'string' && inputs ? inputs.get(fld.input) : undefined;
      formFields.set(fld.name, input ? typeClass(model, input.type) : 'any');
    }
    list(d.fields).forEach((fld, i) => {
      if (!isObj(fld)) return;
      const sub = ['fields', i];
      if (typeof fld.name === 'string') {
        if (names.has(fld.name)) err('form.field-duplicate', f, `Form "${f.id}" has two fields named "${fld.name}".`, [...sub, 'name']);
        names.add(fld.name);
      }
      if (fld.label !== undefined && !nonEmpty(fld.label)) err('form.label-empty', f, `Field "${fld.name}" of form "${f.id}" has an empty label; a control needs an accessible name.`, [...sub, 'label']);
      const choice = CHOICE_CONTROLS.includes(fld.control);
      const listed = Array.isArray(fld.options) && fld.options.length > 0;
      if (choice ? listed === (fld.optionsFrom !== undefined) : fld.options !== undefined || fld.optionsFrom !== undefined) {
        err('form.options', f, choice ? `Field "${fld.name}" of form "${f.id}" is a ${fld.control}, so it lists its "options" or takes them from the view model ("optionsFrom"), one of the two.` : `Field "${fld.name}" of form "${f.id}" is not a select or radio, so it has no "options" or "optionsFrom".`, [...sub, choice ? 'control' : fld.options !== undefined ? 'options' : 'optionsFrom']);
      }
      list(fld.options).forEach((o, j) => { if (isObj(o) && o.label !== undefined && !nonEmpty(o.label)) err('form.label-empty', f, `Option ${j + 1} of field "${fld.name}" of form "${f.id}" has an empty label.`, [...sub, 'options', j, 'label']); });
      if (choice && fld.optionsFrom !== undefined && !listed) checkOptionsFrom(f, fld, sub, screen);
      checkDerive(f, fld, sub, scope, formFields);
      if (fld.initial !== undefined) {
        if (fld.derive !== undefined && fld.until === undefined) err('form.initial', f, `Field "${fld.name}" of form "${f.id}" is always derived, so an initial value would never be seen.`, [...sub, 'initial']);
        else checkInitial(f, fld, sub, screen, scope);
      }
      if (fld.normalize !== undefined && !TYPED_CONTROLS.includes(fld.control)) err('form.normalize', f, `Field "${fld.name}" of form "${f.id}" trims its value, which only a text, textarea or password control holds.`, [...sub, 'normalize']);
      if (typeof fld.input !== 'string' || !inputs) return;
      const input = inputs.get(fld.input);
      if (!input) { err('form.field-unknown', f, `Contract "${contract?.id}" has no input "${fld.input}".`, [...sub, 'input']); return; }
      if (suppliedInputs(contract).has(fld.input)) { err('form.supplied-input', f, `Input "${fld.input}" of contract "${contract?.id}" is supplied by its ${suppliedInputs(contract).get(fld.input)}, never by the body, so a field of form "${f.id}" cannot fill it.`, [...sub, 'input']); return; }
      if (filled.has(fld.input)) err('form.field-duplicate', f, `Input "${fld.input}" is filled by two fields of form "${f.id}".`, [...sub, 'input']);
      filled.add(fld.input);
      const cls = typeClass(model, input.type);
      const fits = CONTROL_CLASSES[fld.control];
      if (fits && cls !== 'any' && !fits.includes(cls)) err('form.control-type', f, `A ${fld.control} control edits a ${fits.join(' or a ')}, but input "${fld.input}" of contract "${contract?.id}" is a ${cls}.`, [...sub, 'control']);
    });
    if (d.submitLabel !== undefined && !nonEmpty(d.submitLabel)) err('form.label-empty', f, `Form "${f.id}" has an empty submit label; its button needs an accessible name.`, ['submitLabel']);
    if (isObj(d.arguments) && inputs) {
      for (const name of Object.keys(d.arguments)) if (filled.has(name)) err('form.field-duplicate', f, `Input "${name}" is filled by a field and by an argument of form "${f.id}".`, ['arguments', name]);
    }
    checkArguments(f, d.arguments, contract, scope);
    if (inputs) {
      for (const [name, input] of inputs) {
        if (input.optional !== true && !filled.has(name) && !suppliedInputs(contract).has(name) && !(isObj(d.arguments) && Object.hasOwn(d.arguments, name))) err('form.input-uncovered', f, `Form "${f.id}" submits to contract "${contract?.id}" but neither a field nor an argument fills its input "${name}".`, ['contract']);
      }
    }
    checkDeriveCycles(f);
    const outcome = outcomeScope(scope, contract, formFields);
    // then: a second call when the first succeeds; its arguments read the first call's response. The outcome
    // reads both calls' outputs, the second's where both have one.
    let outcomeContract = contract;
    if (d.then !== undefined) {
      const th = d.then;
      if (!isObj(th) || typeof th.contract !== 'string' || Object.keys(th).some((k) => k !== 'contract' && k !== 'arguments') || (th.arguments !== undefined && !isObj(th.arguments))) {
        err('form.then', f, `The second call of form "${f.id}" is {contract, arguments?}: a contract and input -> expression.`, ['then']);
      } else {
        const second = get(th.contract, 'contract');
        checkArguments(f, th.arguments, second, outcome, ['then', 'arguments']);
        if (second && contract) {
          const secondOuts = list(second.data.outputs).filter(isObj);
          const outputs = [...list(contract.data.outputs).filter((o) => isObj(o) && !secondOuts.some((s) => s.name === o.name)), ...secondOuts];
          outcome.set('response', classes(outputs));
          outcomeContract = /** @type {Entity} */ ({ ...contract, data: { ...contract.data, outputs } });
        }
      }
    }
    checkNavigate(f, outcome);
    checkToast(f, outcome, outcomeContract, screen);
    checkViewOverlay(f, outcome, screen);
    checkOnError(f);
  }

  /**
   * result of an action: {into, output}. The call's output is placed in a screen-local value of the action's
   * screen, of the same type, and the page stays where it is (no navigation).
   * @param {Entity} a @param {Entity|undefined} contract @param {Entity|undefined} screen
   */
  const checkResult = (a, contract, screen) => {
    const r = a.data.result;
    /** @param {string} why @param {(string|number)[]} [where] */
    const bad = (why, where = ['result']) => err('action.result', a, `Action "${a.id}" keeps its result on the screen: ${why}.`, where);
    if (!isObj(r) || typeof r.into !== 'string' || typeof r.output !== 'string' || Object.keys(r).some((k) => k !== 'into' && k !== 'output')) { bad('"result" is {into, output}: a screen-local value and an output of the contract'); return; }
    if (isObj(a.data.onSuccess) && a.data.onSuccess.navigate !== undefined) bad('an action that keeps its result on the screen does not also navigate away', ['onSuccess', 'navigate']);
    const locals = screen ? screenLocals.get(screen.id) : undefined;
    const into = locals?.get(r.into);
    if (screen && into === undefined) bad(`screen "${screen.id}" declares no screen-local value "${r.into}" (in "local")`, ['result', 'into']);
    const out = contract ? fieldMap(contract.data.outputs).get(r.output) : undefined;
    if (contract && !out) { bad(`contract "${contract.id}" has no output "${r.output}"`, ['result', 'output']); return; }
    const norm = (/** @type {any} */ t) => (typeof t === 'string' ? t.replace(/\s+/g, '') : '');
    if (out && into !== undefined && norm(out.type) !== norm(into)) bad(`output "${r.output}" of contract "${contract?.id}" is of type "${out.type}", but screen-local value "${r.into}" is of type "${into}"`, ['result', 'into']);
  };

  /**
   * alsoOn of an action: {auth}; the action is offered on every other screen of that authentication, so it
   * reads nothing of one screen (route, query, view, local, item, form) and is not per-row, kept or reading a form.
   * @param {Entity} a
   */
  const checkAlsoOn = (a) => {
    const d = a.data;
    /** @param {string} why @param {(string|number)[]} [where] */
    const bad = (why, where = ['alsoOn']) => err('action.also-on', a, `Action "${a.id}" is also offered on other screens: ${why}.`, where);
    if (!isObj(d.alsoOn) || typeof d.alsoOn.auth !== 'string' || Object.keys(d.alsoOn).some((k) => k !== 'auth')) { bad('"alsoOn" is {auth}'); return; }
    if (!AUTH_RE.test(d.alsoOn.auth)) { bad(`authentication ${JSON.stringify(d.alsoOn.auth)} is not none, session or role:<role>`, ['alsoOn', 'auth']); return; }
    for (const k of ['forEach', 'form', 'result']) if (d[k] !== undefined) bad(`"${k}" belongs to one screen`, [k]);
    /** @type {[any, (string|number)[]][]} */
    const exprs = [];
    if (isObj(d.arguments)) for (const [n, s] of Object.entries(d.arguments)) exprs.push([s, ['arguments', n]]);
    const nav = isObj(d.onSuccess) && isObj(d.onSuccess.navigate) ? d.onSuccess.navigate : undefined;
    if (nav && isObj(nav.params)) for (const [n, s] of Object.entries(nav.params)) exprs.push([s, ['onSuccess', 'navigate', 'params', n]]);
    if (nav && nav.path !== undefined) exprs.push([nav.path, ['onSuccess', 'navigate', 'path']]);
    if (isObj(d.onSuccess) && isObj(d.onSuccess.view)) for (const [n, s] of Object.entries(d.onSuccess.view)) exprs.push([s, ['onSuccess', 'view', n]]);
    for (const [src, where] of exprs) {
      const parsed = typeof src === 'string' ? parseExpr(src) : undefined;
      const head = parsed?.ok ? exprRefs(parsed.ast).map((r) => r[0]).find((h) => SCREEN_SCOPES.includes(h)) : undefined;
      if (head) bad(`"${src}" reads ${head}.<name>, which differs from screen to screen`, where);
    }
    const toast = isObj(d.onSuccess) && typeof d.onSuccess.toast === 'string' ? d.onSuccess.toast : '';
    for (const m of toast.matchAll(PLACEHOLDER_RE)) {
      if (SCREEN_SCOPES.includes(m[1].split('.')[0])) bad(`the toast reads ${m[0]}, which differs from screen to screen`, ['onSuccess', 'toast']);
    }
  };

  // --- actions ----------------------------------------------------------------
  for (const a of kind('action')) {
    const d = a.data;
    const contract = get(d.contract, 'contract');
    const screen = get(d.screen, 'screen');
    if (d.label !== undefined && !nonEmpty(d.label)) err('action.label-empty', a, `Action "${a.id}" has an empty label; its button needs an accessible name.`, ['label']);
    const scope = screenScope(screen);
    // An action that names a form of its screen (form) also reads form.<field>: the values being edited.
    /** @type {Map<string, TypeClass>|undefined} */
    let formFields;
    if (d.form !== undefined) {
      const fm = get(d.form, 'form');
      if (fm && fm.data.screen !== d.screen) err('action.form', a, `Action "${a.id}" reads form "${fm.id}", which belongs to screen "${fm.data.screen}", not to the action's screen "${d.screen}".`, ['form']);
      if (fm) {
        const fc = get(fm.data.contract, 'contract');
        const fin = fc ? fieldMap(fc.data.inputs) : undefined;
        formFields = new Map();
        for (const fld of list(fm.data.fields)) {
          if (!isObj(fld) || typeof fld.name !== 'string') continue;
          const input = typeof fld.input === 'string' && fin ? fin.get(fld.input) : undefined;
          formFields.set(fld.name, input ? typeClass(model, input.type) : 'any');
        }
        scope.set('form', formFields);
      }
    }
    // A per-row action repeats over a list in the view model; item.<field> is one row in its label,
    // confirmation (as ${item.<field>}) and expressions.
    /** @type {Map<string, TypeClass>|undefined} */
    let item;
    if (d.forEach !== undefined) {
      const vm = screen ? get(screen.data.viewModel, 'contract') : undefined;
      const r = typeof d.forEach !== 'string' ? { error: 'it is not a path' } : vm ? viewPathType(model, vm, d.forEach) : { error: `screen "${screen?.id}" names no view-model contract` };
      const text = typeof r.type === 'string' ? r.type.trim() : '';
      const m = /^list<(.+)>$/.exec(text);
      const el = m ? model.entities.get(m[1].trim()) : undefined;
      const problem = r.error ?? (!m ? `it reaches ${text ? `a value of type "${text}"` : 'a value of unknown type'}, not a list` : el?.kind !== 'type' || el.data.kind !== 'struct' ? `its items are "${m[1].trim()}", not a declared struct, so item.<field> has no fields` : undefined);
      if (problem) { if (screen) err('action.for-each', a, `Action "${a.id}" repeats for each "${d.forEach}" of the view model: ${problem}.`, ['forEach']); }
      else if (el) item = classes(el.data.fields);
    }
    for (const prop of ['label', 'confirm']) {
      const { fields, bad } = itemPlaceholders(d[prop]);
      for (const p of bad) err('action.label-template', a, `The ${prop} of action "${a.id}" has placeholder "${p}"; only \${item.<field>} of a per-row action is filled in.`, [prop]);
      for (const f of fields) {
        if (d.forEach === undefined) err('action.label-template', a, `The ${prop} of action "${a.id}" reads item.${f}, but the action is not repeated per row ("forEach").`, [prop]);
        else if (item && !item.has(f)) err('action.label-template', a, `The ${prop} of action "${a.id}" reads item.${f}, which is not a field of the rows of "${d.forEach}".`, [prop]);
      }
    }
    // A per-row action whose rows could not be resolved (reported above, or its screen is unresolved) reads
    // item fields of unknown class, so one broken forEach is one error.
    if (d.forEach !== undefined) scope.set('item', item ?? new AnyFields());
    checkArguments(a, d.arguments, contract, scope);
    if (contract) {
      for (const [name, input] of fieldMap(contract.data.inputs)) {
        if (input.optional !== true && !suppliedInputs(contract).has(name) && !(isObj(d.arguments) && Object.hasOwn(d.arguments, name))) err('action.argument-missing', a, `Action "${a.id}" calls contract "${contract.id}" but gives no argument for its input "${name}".`, ['arguments']);
      }
    }
    if (d.result !== undefined) checkResult(a, contract, screen);
    const outcome = outcomeScope(scope, contract, formFields);
    checkNavigate(a, outcome);
    checkToast(a, outcome, contract, screen);
    checkViewOverlay(a, outcome, screen);
    checkOnError(a);
    if (d.confirmAnnounce !== undefined && (d.confirm === undefined || !nonEmpty(d.confirmAnnounce))) err('action.confirm-announce', a, d.confirm === undefined ? `Action "${a.id}" announces its confirmation but asks for none ("confirm").` : `What action "${a.id}" announces when it asks for its confirmation is empty.`, ['confirmAnnounce']);
    if (d.alsoOn !== undefined) checkAlsoOn(a);
  }

  /**
   * when of a live binding: the condition under which an occurrence refreshes the screen. An expression (a
   * boolean) over event.<payload field> and the screen's scope; {value, in}: the value of an expression is an
   * item of the list a view-model path reaches; {any: [condition]} and {all: [condition]}: some, every one.
   * @param {Entity} b @param {any} c @param {(string|number)[]} at @param {Map<string, Map<string, TypeClass>>} scope @param {Entity|undefined} screen
   */
  const checkWhen = (b, c, at, scope, screen) => {
    /** @param {string} why @param {(string|number)[]} [where] */
    const bad = (why, where = at) => err('liveBinding.when', b, `The condition of live binding "${b.id}": ${why}.`, where);
    if (typeof c === 'string') { checkExpr(b, c, at, scope, (cls) => (cls === 'bool' || cls === 'any' ? undefined : `it is a ${cls}, and a condition is a boolean`)); return; }
    const keys = isObj(c) ? Object.keys(c).sort().join(',') : '';
    if (keys === 'any' || keys === 'all') {
      const items = c[keys];
      if (!Array.isArray(items) || !items.length) { bad(`"${keys}" is a non-empty list of conditions`, [...at, keys]); return; }
      items.forEach((x, i) => checkWhen(b, x, [...at, keys, i], scope, screen));
      return;
    }
    if (keys !== 'in,value' || typeof c.in !== 'string') { bad('a condition is an expression, {value, in: view-model path}, {any: [condition]} or {all: [condition]}'); return; }
    const vm = screen ? get(screen.data.viewModel, 'contract') : undefined;
    /** @type {TypeClass} */
    let item = 'any';
    if (!vm) { if (screen) bad(`screen "${screen.id}" names no view-model contract, so "in" has no list to read`, [...at, 'in']); }
    else {
      const r = viewPathType(model, vm, c.in);
      const text = typeof r.type === 'string' ? r.type.trim() : '';
      const m = /^list<(.+)>$/.exec(text);
      if (r.error) bad(r.error, [...at, 'in']);
      else if (r.type !== undefined && !m) bad(`"${c.in}" reaches a value of type "${text}", not a list`, [...at, 'in']);
      else if (m) item = typeClass(model, m[1].trim());
    }
    checkExpr(b, c.value, [...at, 'value'], scope, (cls) => (cls === item || cls === 'any' || item === 'any' ? undefined : `it is a ${cls}, but the items of "${c.in}" are ${item === 'struct' || item === 'list' ? `${item}s` : `of class ${item}`}`));
  };

  // --- live bindings -------------------------------------------------------------
  /** @type {Set<string>} */
  const bound = new Set();
  for (const b of kind('liveBinding')) {
    const d = b.data;
    const key = `${d.screen}|${d.event}`;
    if (bound.has(key)) err('liveBinding.duplicate', b, `Screen "${d.screen}" is already refreshed by event "${d.event}" through another live binding.`, ['event']);
    bound.add(key);
    const screen = get(d.screen, 'screen');
    if (d.when !== undefined) {
      const ev = get(d.event, 'event');
      const scope = screenScope(screen);
      scope.set('event', ev ? classes(ev.data.payload) : new AnyFields());
      checkWhen(b, d.when, ['when'], scope, screen);
    }
    if (typeof d.refresh !== 'string' || d.refresh === 'whole') continue;
    const vm = screen ? get(screen.data.viewModel, 'contract') : undefined;
    if (!vm) { if (screen) err('liveBinding.refresh', b, `Live binding "${b.id}" refreshes "${d.refresh}" of screen "${screen.id}", which names no view-model contract; only "whole" applies.`, ['refresh']); continue; }
    const problem = viewPathType(model, vm, d.refresh).error;
    if (problem) err('liveBinding.refresh', b, `Live binding "${b.id}" refreshes "${d.refresh}": ${problem}.`, ['refresh']);
  }

  // --- error messages ------------------------------------------------------------
  /** The contracts a form or action calls (a form's second call too), whose errors it can meet. @param {Entity} o @returns {Entity[]} */
  const calls = (o) => /** @type {Entity[]} */ ([get(o.data.contract, 'contract'), o.kind === 'form' && isObj(o.data.then) ? get(o.data.then.contract, 'contract') : undefined].filter((c) => c !== undefined));
  /** @type {Entity[]} */
  const seenMessages = [];
  for (const m of kind('errorMessage')) {
    const d = m.data;
    const on = d.on === 'check' || d.on === 'error' ? d.on : undefined;
    const kinds = Array.isArray(d.kinds) ? d.kinds : undefined;
    if (d.kinds !== undefined) {
      if (!kinds || !kinds.length) err('errorMessage.kinds', m, `Error message "${m.id}" lists no kinds; leave "kinds" out for the default.`, ['kinds']);
      list(kinds).forEach((k, i) => {
        if (typeof k !== 'string' || !KIND_RE.test(k)) err('errorMessage.kinds', m, `Kind ${JSON.stringify(k)} of error message "${m.id}" is not a name (a lower-case letter, then letters, digits, _ or -).`, ['kinds', i]);
        else if (kinds?.indexOf(k) !== i) err('errorMessage.kinds', m, `Error message "${m.id}" lists kind "${k}" twice.`, ['kinds', i]);
      });
    }
    /** @type {Entity[]|undefined} */
    const owners = Array.isArray(d.appliesTo) ? d.appliesTo.map((/** @type {any} */ id) => model.entities.get(id)).filter((/** @type {any} */ e) => e && (e.kind === 'form' || e.kind === 'action')) : undefined;
    if (d.appliesTo !== undefined && (!Array.isArray(d.appliesTo) || !d.appliesTo.length)) err('errorMessage.applies-to', m, `Error message "${m.id}" applies to nothing; leave "appliesTo" out to word every form and action.`, ['appliesTo']);
    else list(d.appliesTo).forEach((id, i) => { if (d.appliesTo.indexOf(id) !== i) err('errorMessage.applies-to', m, `Error message "${m.id}" applies to "${id}" twice.`, ['appliesTo', i]); });
    if (on === 'error' && kinds) {
      const contracts = owners ? owners.flatMap(calls) : kind('contract');
      const codes = new Set(contracts.flatMap((c) => list(c.data.errors).filter(isObj).map((x) => x.name)));
      kinds.forEach((k, i) => { if (typeof k === 'string' && KIND_RE.test(k) && !codes.has(k)) err('errorMessage.kinds', m, `Error message "${m.id}" words error "${k}", which no contract ${owners ? 'its forms and actions call ' : ''}answers.`, ['kinds', i]); });
    }
    if (d.field !== undefined && on !== 'check') err('errorMessage.field', m, `Error message "${m.id}" is shown on a field, which only a message on a failed check can be.`, ['field']);
    if (on) {
      for (const prop of ['text', 'fallback']) {
        if (typeof d[prop] !== 'string') continue;
        if (!nonEmpty(d[prop])) { err('errorMessage.template', m, `The ${prop} of error message "${m.id}" is empty.`, [prop]); continue; }
        for (const ph of d[prop].matchAll(PLACEHOLDER_RE)) {
          if (!MESSAGE_PLACEHOLDERS[on].includes(ph[1])) err('errorMessage.template', m, `The ${prop} of error message "${m.id}" has placeholder "${ph[0]}"; a message on ${on === 'check' ? 'a failed check' : 'an error'} fills in ${MESSAGE_PLACEHOLDERS[on].map((x) => '${' + x + '}').join(', ')}.`, [prop]);
        }
      }
    }
    // Two messages wording the same thing for the same forms and actions: which one applies is not decided.
    for (const other of seenMessages) {
      const o = other.data;
      if (o.on !== d.on) continue;
      const ok = Array.isArray(o.kinds) ? o.kinds : undefined;
      const sameKinds = !kinds && !ok ? true : kinds && ok ? kinds.some((k) => ok.includes(k)) : false;
      const oa = Array.isArray(o.appliesTo) ? o.appliesTo : undefined;
      const da = Array.isArray(d.appliesTo) ? d.appliesTo : undefined;
      const sameOwners = !oa && !da ? true : oa && da ? da.some((x) => oa.includes(x)) : false;
      if (sameKinds && sameOwners) { err('errorMessage.duplicate', m, `Error message "${m.id}" words the same ${on === 'check' ? 'check kinds' : 'errors'} as error message "${other.id}", for the same forms and actions.`, [kinds ? 'kinds' : 'on']); break; }
    }
    seenMessages.push(m);
  }

  // --- user journeys -------------------------------------------------------------
  for (const u of kind('uiScenario')) checkJourney(u, err, get, screenParams);
  return out;
}

/**
 * The type a dotted path into the view model of a contract reaches, or why it is not a path: the first
 * segment is an output, every later one a field of the struct type before it (through list<T> and option<T>).
 * A segment after a type nothing is known about (free text) is accepted, and the type is then unknown.
 * @param {Model} model @param {Entity} contract @param {string} path @returns {{type?: any, error?: string}}
 */
function viewPathType(model, contract, path) {
  const segs = path.split('.');
  const first = fieldMap(contract.data.outputs).get(segs[0]);
  if (!first) return { error: `"${segs[0]}" is not an output of contract "${contract.id}"` };
  return typePathType(model, first.type, segs.slice(1));
}

/**
 * The type a path of struct fields reaches from a type (through list<T> and option<T>), or why it is not one.
 * A segment after a type nothing is known about (free text) is accepted, and the type is then unknown.
 * @param {Model} model @param {any} start @param {string[]} segs @returns {{type?: any, error?: string}}
 */
function typePathType(model, start, segs) {
  let type = start;
  for (const seg of segs) {
    let text = typeof type === 'string' ? type.trim() : '';
    for (let m = WRAPPER_RE.exec(text); m; m = WRAPPER_RE.exec(text)) text = m[2].trim();
    const t = model.entities.get(text);
    if (t?.kind !== 'type') {
      if (typeClass(model, text) === 'any') return { type: undefined };
      return { error: `"${seg}" follows a value of type "${text}", which has no fields` };
    }
    if (t.data.kind !== 'struct') return { error: `"${seg}" follows a value of type "${t.id}", which is not a struct` };
    const f = fieldMap(t.data.fields).get(seg);
    if (!f) return { error: `struct "${t.id}" has no field "${seg}"` };
    type = f.type;
  }
  return { type };
}

/**
 * The readiness rules of the user interface: what a generator needs beyond consistency. A contract a form or
 * action uses that policies govern must state policyDefault; that is the construct rule
 * ready.policy-default-missing (constructs.js), which covers every governed contract, so it is not repeated.
 * @param {Model} model @returns {Gap[]}
 */
export function uiReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  /** @param {Entity} e @param {string} code @param {string} message */
  const gap = (e, code, message) => out.push({ code, severity: 'error', message, entityId: e.id });
  for (const s of model.byKind.screen ?? []) {
    if (s.data.viewModel === undefined) gap(s, 'ready.screen-view-model-missing', `Screen "${s.id}" names no contract whose response is its view model ("viewModel").`);
    if (s.data.kind === undefined) gap(s, 'ready.screen-kind-missing', `Screen "${s.id}" names no renderer that draws it ("kind").`);
  }
  for (const f of model.byKind.form ?? []) {
    for (const fld of list(f.data.fields)) {
      if (isObj(fld) && fld.label === undefined) gap(f, 'ready.form-field-label-missing', `Field "${fld.name}" of form "${f.id}" has no label, so its control has no accessible name.`);
    }
  }
  for (const a of model.byKind.action ?? []) {
    if (a.data.onSuccess === undefined) gap(a, 'ready.action-on-success-missing', `Action "${a.id}" does not say what the page does when its call succeeds ("onSuccess").`);
    if (a.data.onError === undefined) gap(a, 'ready.action-on-error-missing', `Action "${a.id}" does not say where a refusal of its call is shown ("onError").`);
  }
  // Every refusal a form or action can meet needs wording: the default message on an error, for all of them.
  const callers = [...(model.byKind.form ?? []), ...(model.byKind.action ?? [])];
  const fallback = (model.byKind.errorMessage ?? []).some((m) => m.data.on === 'error' && m.data.kinds === undefined && m.data.appliesTo === undefined);
  if (callers.length && !fallback) gap(callers[0], 'ready.error-message-default-missing', `No error message words a refusal that no other message words ({on: "error"} without kinds or appliesTo), so a refusal of "${callers[0].id}" or of another form or action may have no text.`);
  return out;
}
