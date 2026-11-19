// The steps of a user journey (uiScenario): what each step kind takes and the rules over a journey's steps.
// Elements are addressed by WAI-ARIA role and accessible name (exact, or a regular expression), optionally a
// heading level and an enclosing element (within), never by CSS selector. Steps can capture values (a cookie,
// a response header, an element's text or attribute, fields of an API reply) and later steps use them as
// ${name} in their strings. Pure and deterministic; run from ui.js. docs/model-and-format.md, "User interface".

import { eventLogging } from './telemetry.js';

/** @typedef {import('./types.js').Entity} Entity */

/** The keys of an element selector. */
const TARGET = ['role', 'name', 'namePattern', 'level', 'within'];

/**
 * The step kinds of a user journey, and the keys each one's value may have (null: a scalar value).
 * @type {Readonly<Record<string, string[]|null>>}
 */
export const STEP_KINDS = Object.freeze({
  goto: ['screen', 'params', 'host'],
  gotoPath: ['path', 'host'],
  reload: [],
  back: [],
  click: TARGET,
  focus: TARGET,
  clickAction: ['action', 'item', 'confirm'],
  fill: ['form', 'field', 'value', ...TARGET],
  submit: ['form'],
  press: null,
  expectText: ['text', 'pattern', 'within', 'timeoutMs'],
  expectNoText: ['text', 'pattern', 'within', 'timeoutMs'],
  expectTitle: ['text', 'pattern', 'timeoutMs'],
  expectScreen: ['screen', 'params', 'timeoutMs'],
  expectRole: [...TARGET, 'state', 'timeoutMs'],
  expectCount: [...TARGET, 'count', 'timeoutMs'],
  expectAttribute: [...TARGET, 'attribute', 'value', 'pattern', 'timeoutMs'],
  expectStatus: null,
  mark: null,
  expectNoReload: null,
  recordRequests: null,
  expectRequests: ['log', 'to', 'only', 'atLeast', 'fromWorker'],
  expectNoRequest: ['log', 'path'],
  apiCall: ['method', 'path', 'host', 'headers', 'body', 'as', 'anonymous', 'expectStatus', 'expectJson', 'expectBodyIncludes', 'expectBodyExcludes', 'capture'],
  expectCookie: ['name', 'absent', 'attributes'],
  setCookie: ['name', 'value', 'host', 'attributes'],
  capture: ['name', 'from', 'cookie', 'header', 'element', 'attribute'],
  emulate: ['colorScheme', 'reducedMotion', 'touch', 'mobile'],
  expectNoOverflow: [],
  expectBeside: ['a', 'b', 'side'],
  switchBrowser: null,
  goOffline: [],
  goOnline: [],
  setViewport: ['width', 'height'],
  axeScan: [],
  logScan: ['forbid'],
  expectLog: ['service', 'event', 'fields', 'timeoutMs'],
  waitFor: ['event', 'timeoutMs'],
  expectNoEvent: ['event', 'forMs'],
});

/** Step kinds whose value may also be written as true (they take no parameters). */
const FLAG_STEPS = ['reload', 'back', 'goOffline', 'goOnline', 'axeScan', 'expectNoOverflow'];

/** WAI-ARIA 1.2 roles a step may select by, abstract roles excluded. */
export const ARIA_ROLES = Object.freeze([
  'alert', 'alertdialog', 'application', 'article', 'banner', 'blockquote', 'button', 'caption', 'cell', 'checkbox',
  'code', 'columnheader', 'combobox', 'complementary', 'contentinfo', 'definition', 'deletion', 'dialog', 'directory',
  'document', 'emphasis', 'feed', 'figure', 'form', 'generic', 'grid', 'gridcell', 'group', 'heading', 'img',
  'insertion', 'link', 'list', 'listbox', 'listitem', 'log', 'main', 'marquee', 'math', 'menu', 'menubar',
  'menuitem', 'menuitemcheckbox', 'menuitemradio', 'meter', 'navigation', 'none', 'note', 'option', 'paragraph',
  'presentation', 'progressbar', 'radio', 'radiogroup', 'region', 'row', 'rowgroup', 'rowheader', 'scrollbar',
  'search', 'searchbox', 'separator', 'slider', 'spinbutton', 'status', 'strong', 'subscript', 'superscript',
  'switch', 'tab', 'table', 'tablist', 'tabpanel', 'term', 'textbox', 'time', 'timer', 'toolbar', 'tooltip', 'tree',
  'treegrid', 'treeitem',
]);

/** Roles a fill step may type into when it names a control by role instead of by form field. */
const FILLABLE_ROLES = ['textbox', 'searchbox', 'combobox', 'spinbutton'];
const STATES = ['visible', 'hidden', 'enabled', 'disabled', 'focused', 'checked', 'unchecked'];
const METHODS = ['GET', 'POST', 'PUT', 'PATCH', 'DELETE'];
const SAME_SITE = ['Strict', 'Lax', 'None'];
const SIDES = ['left', 'right', 'above', 'below'];

/** An attribute of an element a journey may read: ARIA state, application data, a control's value, a link. */
const ELEMENT_ATTRIBUTE_RE = /^(?:aria-[a-z]+|data-[a-z][a-z0-9-]*|value|href|lang|dir)$/;
/** An attribute of the document element a journey may read. */
const ROOT_ATTRIBUTE_RE = /^(?:data-[a-z][a-z0-9-]*|lang|dir)$/;
const HOST_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?)*(?::\d{1,5})?$/;
const PATH_RE = /^\/[^\s#]*$/;
const CAPTURE_NAME_RE = /^[A-Za-z_][A-Za-z0-9_]*$/;
const JSON_PATH_RE = /^[A-Za-z0-9_$-]+(?:\.[A-Za-z0-9_$-]+)*$/;
const REF_RE = /\$\{([^}]*)\}/g;
const ITEM_REF_RE = /\$\{item\.([A-Za-z_][A-Za-z0-9_]*)\}/g;

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v */
const nonEmpty = (v) => typeof v === 'string' && v.trim() !== '';
/** @param {any} v */
const posInt = (v) => Number.isInteger(v) && v >= 1;

/**
 * The fields of the row item an action label or confirmation reads (${item.<field>}), and the placeholders
 * that are not of that form.
 * @param {any} text @returns {{fields: string[], bad: string[]}}
 */
export function itemPlaceholders(text) {
  if (typeof text !== 'string') return { fields: [], bad: [] };
  const fields = [...text.matchAll(ITEM_REF_RE)].map((m) => m[1]);
  const bad = [...text.matchAll(REF_RE)].map((m) => m[0]).filter((p) => !/^\$\{item\.[A-Za-z_][A-Za-z0-9_]*\}$/.test(p));
  return { fields, bad };
}

/**
 * Whether a regular expression compiles once its ${name} references are replaced by plain text.
 * @param {any} p
 */
const compiles = (p) => {
  if (typeof p !== 'string' || p === '') return false;
  try { new RegExp(p.replace(REF_RE, 'x'), 'u'); return true; } catch { return false; }
};

/**
 * Every string inside a value, with its path: the places a ${name} reference may appear.
 * @param {any} v @param {(string|number)[]} at @param {(s: string, at: (string|number)[]) => void} visit
 */
const strings = (v, at, visit) => {
  if (typeof v === 'string') visit(v, at);
  else if (Array.isArray(v)) v.forEach((x, i) => strings(x, [...at, i], visit));
  else if (isObj(v)) for (const [k, x] of Object.entries(v)) strings(x, [...at, k], visit);
};

/**
 * The rules of one user journey: browsers and viewport, the requirements it verifies, and every step.
 * @param {Entity} u
 * @param {(code: string, e: Entity, message: string, sub?: (string|number)[]) => void} err
 * @param {(id: any, k: string) => Entity|undefined} get
 * @param {Map<string, {params: string[], query: string[], catchAll?: boolean}>} screenParams
 */
export function checkJourney(u, err, get, screenParams) {
  const d = u.data;
  const browsers = list(d.browsers);
  browsers.forEach((b, i) => {
    if (!nonEmpty(b)) err('uiScenario.browsers', u, `Browser ${i + 1} of journey "${u.id}" has no name.`, ['browsers', i]);
    else if (browsers.indexOf(b) !== i) err('uiScenario.browsers', u, `Journey "${u.id}" names browser "${b}" twice.`, ['browsers', i]);
  });
  if (isObj(d.viewport) && !(posInt(d.viewport.width) && posInt(d.viewport.height))) err('uiScenario.viewport', u, `The viewport of journey "${u.id}" needs a positive integer width and height.`, ['viewport']);
  list(d.verifies).forEach((id, i) => {
    const c = get(id, 'claim');
    if (c && c.data.kind !== 'requirement') err('uiScenario.verifies-not-requirement', u, `Journey "${u.id}" verifies "${id}", which is a ${c.data.kind} claim, not a requirement.`, ['verifies', i]);
  });

  // What the journey has defined so far: captured values (shared by every browser), and the page markers
  // and request logs of each browser (they live in that browser's page).
  /** @type {Set<string>} */
  const captured = new Set();
  let browser = browsers[0] ?? '';
  /** @type {Map<string, Set<string>>} */
  const marks = new Map();
  /** @type {Map<string, Set<string>>} */
  const logs = new Map();
  const inBrowser = (/** @type {Map<string, Set<string>>} */ m) => { if (!m.has(browser)) m.set(browser, new Set()); return /** @type {Set<string>} */ (m.get(browser)); };

  list(d.steps).forEach((step, i) => {
    const at = ['steps', i];
    const keys = isObj(step) ? Object.keys(step) : [];
    const known = keys.filter((k) => Object.hasOwn(STEP_KINDS, k));
    if (keys.length !== 1 || known.length !== 1) {
      err('uiScenario.step', u, `Step ${i + 1} of journey "${u.id}" must have exactly one key, one of ${Object.keys(STEP_KINDS).join(', ')}; it has ${keys.length ? keys.join(', ') : 'none'}.`, at);
      return;
    }
    const k = known[0];
    let v = step[k];
    const sub = [...at, k];
    /** @param {string} what @param {(string|number)[]} [where] */
    const bad = (what, where = sub) => err('uiScenario.step', u, `Step ${i + 1} (${k}) of journey "${u.id}": ${what}.`, where);
    /** @param {string} code @param {string} what @param {(string|number)[]} [where] */
    const fail = (code, what, where = sub) => err(code, u, `Step ${i + 1} (${k}) of journey "${u.id}": ${what}.`, where);
    const ref = (/** @type {string} */ what, /** @type {string} */ msg) => fail('uiScenario.step-reference', msg, [...sub, what]);

    // Uses of captured values come first: a step may use only what an earlier step captured.
    strings(v, sub, (s, where) => {
      for (const m of s.matchAll(REF_RE)) {
        if (k === 'capture' && where.length === sub.length + 1 && where[where.length - 1] === 'name') continue;
        if (!CAPTURE_NAME_RE.test(m[1]) || !captured.has(m[1])) fail('uiScenario.capture-undefined', `"${m[0]}" uses a value no earlier step captured${captured.size ? ` (captured so far: ${[...captured].join(', ')})` : ''}`, where);
      }
    });

    if (FLAG_STEPS.includes(k) && v === true) v = {};
    if (k === 'expectScreen' && typeof v === 'string') v = { screen: v };
    const allowed = STEP_KINDS[k];
    if (allowed !== null) {
      if (!isObj(v)) { bad(`the value is an object with ${allowed.length ? allowed.join(', ') : 'no keys'}`); return; }
      const extra = Object.keys(v).filter((x) => !allowed.includes(x));
      if (extra.length) { bad(`${extra.join(', ')} ${extra.length > 1 ? 'are' : 'is'} not part of this step (elements are selected by role and accessible name only)`); return; }
    }

    /**
     * An element selector: a WAI-ARIA role, an accessible name (exact or a pattern), a heading level, and
     * the element it is within.
     * @param {any} t @param {(string|number)[]} where @param {{name?: 'required'|'optional', keys?: boolean}} [opts]
     */
    const target = (t, where, opts = {}) => {
      if (!isObj(t)) { bad('an element is {role, name or namePattern, level?, within?}', where); return; }
      if (opts.keys) {
        const extra = Object.keys(t).filter((x) => !TARGET.includes(x));
        if (extra.length) { bad(`${extra.join(', ')} ${extra.length > 1 ? 'are' : 'is'} not part of an element (role, name, namePattern, level, within)`, where); return; }
      }
      if (typeof t.role !== 'string') bad('an element needs a "role"', where);
      else if (!ARIA_ROLES.includes(t.role)) fail('uiScenario.role', `role "${t.role}" is not a WAI-ARIA role`, [...where, 'role']);
      if (t.name !== undefined && t.namePattern !== undefined) bad('an element has a "name" or a "namePattern", not both', where);
      else if (t.name === undefined && t.namePattern === undefined) { if ((opts.name ?? 'required') === 'required') bad('an element needs a "name" (its accessible name) or a "namePattern"', where); }
      else if (t.name !== undefined) { if (!nonEmpty(t.name)) fail('uiScenario.name-empty', 'an accessible name is empty', [...where, 'name']); }
      else if (!compiles(t.namePattern)) fail('uiScenario.pattern', `name pattern ${JSON.stringify(t.namePattern)} is not a regular expression`, [...where, 'namePattern']);
      if (t.level !== undefined && (t.role !== 'heading' || !(Number.isInteger(t.level) && t.level >= 1 && t.level <= 6))) fail('uiScenario.level', `"level" applies to a heading and is 1 to 6; this element is ${t.role === 'heading' ? `level ${JSON.stringify(t.level)}` : `a ${t.role}`}`, [...where, 'level']);
      if (t.within !== undefined) target(t.within, [...where, 'within'], { name: 'optional', keys: true });
    };
    /** Exactly one of text and pattern. */
    const textOrPattern = () => {
      if ((v.text === undefined) === (v.pattern === undefined)) { bad('it needs exactly one of "text" and "pattern"'); return; }
      if (v.text !== undefined && !nonEmpty(v.text)) bad('"text" is not empty');
      if (v.pattern !== undefined && !compiles(v.pattern)) fail('uiScenario.pattern', `pattern ${JSON.stringify(v.pattern)} is not a regular expression`, [...sub, 'pattern']);
    };
    const timeout = (/** @type {string} */ key = 'timeoutMs') => {
      if (v[key] !== undefined && !posInt(v[key])) fail('uiScenario.timeout', `"${key}" is a positive integer of milliseconds`, [...sub, key]);
    };
    const host = () => {
      if (v.host !== undefined && !(typeof v.host === 'string' && HOST_RE.test(v.host.replace(REF_RE, 'x')))) fail('uiScenario.host', `host ${JSON.stringify(v.host)} is not a host name with an optional port`, [...sub, 'host']);
    };
    const path = (/** @type {any} */ p) => {
      if (!(typeof p === 'string' && PATH_RE.test(p.replace(REF_RE, 'x')))) fail('uiScenario.path', `path ${JSON.stringify(p)} is not an absolute path ("/..." without spaces or a fragment)`, [...sub, 'path']);
    };
    const screenParamsGiven = (/** @type {Entity} */ s, /** @type {any} */ params) => {
      const p = screenParams.get(s.id) ?? { params: [], query: [] };
      const given = isObj(params) ? params : {};
      const missing = p.params.filter((n) => !Object.hasOwn(given, n));
      const extra = Object.keys(given).filter((n) => !p.params.includes(n) && !p.query.includes(n));
      const nonScalar = Object.keys(given).filter((n) => typeof given[n] !== 'string' && typeof given[n] !== 'number');
      if (missing.length || extra.length || nonScalar.length || (params !== undefined && !isObj(params))) fail('uiScenario.goto-params', `screen "${s.id}" (${s.data.route}) has route parameters ${p.params.length ? p.params.join(', ') : 'none'}${missing.length ? `; missing ${missing.join(', ')}` : ''}${extra.length ? `; not parameters of it: ${extra.join(', ')}` : ''}${nonScalar.length ? `; not a string or number: ${nonScalar.join(', ')}` : ''}`, [...sub, 'params']);
    };
    const jsonPath = (/** @type {any} */ p, /** @type {(string|number)[]} */ where) => {
      if (!(typeof p === 'string' && JSON_PATH_RE.test(p))) fail('uiScenario.json-path', `${JSON.stringify(p)} is not a path into a JSON reply (names and indexes joined by ".")`, where);
    };
    const define = (/** @type {any} */ name, /** @type {(string|number)[]} */ where) => {
      if (!(typeof name === 'string' && CAPTURE_NAME_RE.test(name))) { bad('a captured value is named by a letter or _, then letters, digits or _', where); return; }
      if (captured.has(name)) fail('uiScenario.capture-duplicate', `value "${name}" is already captured by an earlier step`, where);
      captured.add(name);
    };
    const cookieAttributes = (/** @type {any} */ a) => {
      if (a === undefined) return;
      const keys = ['secure', 'httpOnly', 'sameSite', 'path', 'hostPrefix'];
      if (!isObj(a) || Object.keys(a).some((x) => !keys.includes(x))) { bad(`"attributes" is an object of ${keys.join(', ')}`, [...sub, 'attributes']); return; }
      for (const b of ['secure', 'httpOnly', 'hostPrefix']) if (a[b] !== undefined && typeof a[b] !== 'boolean') bad(`"${b}" is a boolean`, [...sub, 'attributes', b]);
      if (a.sameSite !== undefined && !SAME_SITE.includes(a.sameSite)) bad(`"sameSite" is ${SAME_SITE.join(', ')}`, [...sub, 'attributes', 'sameSite']);
      if (a.path !== undefined && !(typeof a.path === 'string' && PATH_RE.test(a.path))) fail('uiScenario.path', `cookie path ${JSON.stringify(a.path)} is not an absolute path`, [...sub, 'attributes', 'path']);
    };

    switch (k) {
      case 'goto': {
        host();
        if (typeof v.screen !== 'string') { bad('it needs a "screen"'); break; }
        const s = get(v.screen, 'screen');
        if (!s) { ref('screen', `"${v.screen}" is not a screen`); break; }
        if (screenParams.get(s.id)?.catchAll) { fail('uiScenario.goto-params', `screen "${s.id}" is the catch-all screen and has no address of its own; open an address no screen answers with gotoPath`, [...sub, 'screen']); break; }
        screenParamsGiven(s, v.params);
        break;
      }
      case 'gotoPath': path(v.path); host(); break;
      case 'click': case 'focus': target(v, sub); break;
      case 'clickAction': {
        if (typeof v.action !== 'string') { bad('it needs an "action"'); break; }
        const a = get(v.action, 'action');
        if (!a) { ref('action', `"${v.action}" is not an action`); break; }
        if (v.confirm !== undefined && typeof v.confirm !== 'boolean') { bad('"confirm" is a boolean'); break; }
        if (v.confirm === true && a.data.confirm === undefined) fail('uiScenario.action-item', `action "${a.id}" asks for no confirmation, so "confirm" does not apply`, [...sub, 'confirm']);
        const perRow = a.data.forEach !== undefined;
        if (!perRow) { if (v.item !== undefined) fail('uiScenario.action-item', `action "${a.id}" is not repeated per row (no "forEach"), so it takes no "item"`, [...sub, 'item']); break; }
        const need = [...itemPlaceholders(a.data.label).fields, ...(v.confirm === true ? itemPlaceholders(a.data.confirm).fields : [])];
        const item = isObj(v.item) ? v.item : undefined;
        const missing = [...new Set(need)].filter((f) => !item || typeof item[f] !== 'string' && typeof item[f] !== 'number');
        if (!item || missing.length) fail('uiScenario.action-item', `action "${a.id}" is repeated per row; "item" gives the row's ${need.length ? need.join(', ') : 'fields'} that its label${v.confirm === true ? ' and confirmation' : ''} read${missing.length ? ` (missing ${missing.join(', ')})` : ''}`, [...sub, 'item']);
        break;
      }
      case 'fill': {
        if (!('value' in v) || !['string', 'number', 'boolean'].includes(typeof v.value)) bad('it needs a "value": a string, a number or a boolean');
        if (v.form !== undefined || v.field !== undefined) {
          if (TARGET.some((x) => v[x] !== undefined)) { bad('it names its control by form and field, or by role and name, not both'); break; }
          if (typeof v.form !== 'string' || typeof v.field !== 'string') { bad('it needs both "form" and "field"'); break; }
          const f = get(v.form, 'form');
          if (!f) ref('form', `"${v.form}" is not a form`);
          else if (!list(f.data.fields).some((x) => isObj(x) && x.name === v.field)) ref('field', `form "${f.id}" has no field "${v.field}"`);
        } else {
          target(v, sub);
          if (typeof v.role === 'string' && ARIA_ROLES.includes(v.role) && !FILLABLE_ROLES.includes(v.role)) bad(`a control filled by role is one of ${FILLABLE_ROLES.join(', ')}`);
        }
        break;
      }
      case 'submit': {
        if (typeof v.form !== 'string') bad('it needs a "form"');
        else if (!get(v.form, 'form')) ref('form', `"${v.form}" is not a form`);
        break;
      }
      case 'press': if (!nonEmpty(v)) bad('the value is the key to press, such as Enter or Control+End'); break;
      case 'expectText': case 'expectNoText':
        textOrPattern(); timeout();
        if (v.within !== undefined) target(v.within, [...sub, 'within'], { name: 'optional', keys: true });
        break;
      case 'expectTitle': textOrPattern(); timeout(); break;
      case 'expectScreen': {
        timeout();
        if (typeof v.screen !== 'string') { bad('the value is a screen id, or {screen, params?, timeoutMs?}'); break; }
        const s = get(v.screen, 'screen');
        if (!s) { ref('screen', `"${v.screen}" is not a screen`); break; }
        if (v.params !== undefined) screenParamsGiven(s, v.params);
        break;
      }
      case 'expectRole': {
        const { state, timeoutMs, ...t } = v;
        target(t, sub);
        if (state !== undefined && !STATES.includes(state)) bad(`"state" is ${STATES.join(', ')}`);
        timeout();
        break;
      }
      case 'expectCount': {
        const { count, timeoutMs, ...t } = v;
        target(t, sub, { name: 'optional' });
        if (!(Number.isInteger(count) && count >= 0)) bad('"count" is an integer of at least 0');
        timeout();
        break;
      }
      case 'expectAttribute': {
        const { attribute, value, pattern, timeoutMs, ...t } = v;
        const root = Object.keys(t).length === 0;
        if (!root) target(t, sub);
        if (typeof attribute !== 'string' || !(root ? ROOT_ATTRIBUTE_RE : ELEMENT_ATTRIBUTE_RE).test(attribute)) fail('uiScenario.attribute', root ? `attribute ${JSON.stringify(attribute)} of the document element is not a data-* attribute, lang or dir` : `attribute ${JSON.stringify(attribute)} is not an aria-* or data-* attribute, value, href, lang or dir`, [...sub, 'attribute']);
        if ((value === undefined) === (pattern === undefined)) bad('it needs exactly one of "value" and "pattern"');
        else if (value !== undefined && typeof value !== 'string') bad('"value" is a string');
        else if (pattern !== undefined && !compiles(pattern)) fail('uiScenario.pattern', `pattern ${JSON.stringify(pattern)} is not a regular expression`, [...sub, 'pattern']);
        timeout();
        break;
      }
      case 'expectStatus':
        if (!(Number.isInteger(v) && v >= 100 && v <= 599)) fail('uiScenario.status', `${JSON.stringify(v)} is not an HTTP status, an integer from 100 to 599`);
        break;
      case 'mark': case 'recordRequests':
        if (!(typeof v === 'string' && CAPTURE_NAME_RE.test(v))) bad(`the value is a name for the ${k === 'mark' ? 'marker' : 'request log'}`);
        else inBrowser(k === 'mark' ? marks : logs).add(v);
        break;
      case 'expectNoReload':
        if (typeof v !== 'string') bad('the value is the name of a marker set by a mark step');
        else if (!inBrowser(marks).has(v)) fail('uiScenario.mark-undefined', `marker "${v}" was not set by an earlier mark step in browser ${browser ? `"${browser}"` : '(the only one)'}`);
        break;
      case 'expectRequests': case 'expectNoRequest': {
        if (typeof v.log !== 'string') bad('it needs the "log" a recordRequests step started');
        else if (!inBrowser(logs).has(v.log)) fail('uiScenario.log-undefined', `request log "${v.log}" was not started by an earlier recordRequests step in browser ${browser ? `"${browser}"` : '(the only one)'}`, [...sub, 'log']);
        const p = k === 'expectRequests' ? 'to' : 'path';
        if (!compiles(v[p])) fail('uiScenario.pattern', `"${p}" ${JSON.stringify(v[p])} is not a regular expression`, [...sub, p]);
        if (k === 'expectRequests') {
          if (v.only !== undefined && typeof v.only !== 'boolean') bad('"only" is a boolean');
          if (v.fromWorker !== undefined && typeof v.fromWorker !== 'boolean') bad('"fromWorker" is a boolean');
          if (v.atLeast !== undefined && !(Number.isInteger(v.atLeast) && v.atLeast >= 0)) bad('"atLeast" is an integer of at least 0');
        }
        break;
      }
      case 'apiCall': {
        if (!METHODS.includes(v.method)) bad(`"method" is ${METHODS.join(', ')}`);
        path(v.path); host();
        if (v.headers !== undefined && !(isObj(v.headers) && Object.values(v.headers).every((h) => typeof h === 'string'))) bad('"headers" is an object of strings');
        if (v.anonymous !== undefined && typeof v.anonymous !== 'boolean') bad('"anonymous" is a boolean');
        if (v.as !== undefined) {
          if (v.anonymous === true) bad('a call is made as a browser\'s session or anonymously, not both');
          else if (typeof v.as !== 'string' || !browsers.includes(v.as)) ref('as', `${JSON.stringify(v.as)} is not one of its browsers (${browsers.length ? browsers.join(', ') : 'it names none'})`);
        }
        if (v.expectStatus !== undefined && !(Number.isInteger(v.expectStatus) && v.expectStatus >= 100 && v.expectStatus <= 599)) fail('uiScenario.status', `${JSON.stringify(v.expectStatus)} is not an HTTP status`, [...sub, 'expectStatus']);
        if (v.expectJson !== undefined) {
          if (!isObj(v.expectJson)) bad('"expectJson" maps a path in the reply to its expected value');
          else for (const p of Object.keys(v.expectJson)) jsonPath(p, [...sub, 'expectJson', p]);
        }
        for (const b of ['expectBodyIncludes', 'expectBodyExcludes']) if (v[b] !== undefined && !(Array.isArray(v[b]) && v[b].every(nonEmpty))) bad(`"${b}" is a list of non-empty strings`, [...sub, b]);
        if (v.capture !== undefined) {
          if (!isObj(v.capture)) bad('"capture" maps a value name to a path in the reply');
          else for (const [name, p] of Object.entries(v.capture)) { jsonPath(p, [...sub, 'capture', name]); define(name, [...sub, 'capture', name]); }
        }
        break;
      }
      case 'expectCookie': case 'setCookie': {
        if (!nonEmpty(v.name)) bad('it needs the cookie "name"');
        cookieAttributes(v.attributes);
        if (k === 'expectCookie') {
          if (v.absent !== undefined && typeof v.absent !== 'boolean') bad('"absent" is a boolean');
          if (v.absent === true && v.attributes !== undefined) bad('an absent cookie has no attributes');
        } else {
          if (typeof v.value !== 'string') bad('it needs the cookie "value"');
          if (typeof v.host !== 'string') bad('it needs the "host" the cookie is set for');
          else host();
        }
        break;
      }
      case 'capture': {
        const need = { cookie: ['cookie'], header: ['header'], text: ['element'], attribute: ['element', 'attribute'] };
        const from = /** @type {keyof typeof need} */ (v.from);
        if (!Object.hasOwn(need, from)) bad('"from" is cookie, header, text or attribute');
        else {
          const extra = ['cookie', 'header', 'element', 'attribute'].filter((x) => v[x] !== undefined && !need[from].includes(x));
          const missing = need[from].filter((x) => v[x] === undefined);
          if (extra.length || missing.length) bad(`a capture from ${from} takes ${need[from].join(' and ')}${extra.length ? `, not ${extra.join(', ')}` : ''}`);
          if (v.element !== undefined) target(v.element, [...sub, 'element'], { keys: true });
          if (from === 'attribute' && typeof v.attribute === 'string' && !ELEMENT_ATTRIBUTE_RE.test(v.attribute)) fail('uiScenario.attribute', `attribute "${v.attribute}" is not an aria-* or data-* attribute, value, href, lang or dir`, [...sub, 'attribute']);
        }
        define(v.name, [...sub, 'name']);
        break;
      }
      case 'emulate': {
        const ok = { colorScheme: ['light', 'dark', 'no-preference'], reducedMotion: ['reduce', 'no-preference'] };
        if (!Object.keys(v).length) bad('it sets at least one of colorScheme, reducedMotion, touch and mobile');
        if (v.colorScheme !== undefined && !ok.colorScheme.includes(v.colorScheme)) bad(`"colorScheme" is ${ok.colorScheme.join(', ')}`);
        if (v.reducedMotion !== undefined && !ok.reducedMotion.includes(v.reducedMotion)) bad(`"reducedMotion" is ${ok.reducedMotion.join(', ')}`);
        for (const b of ['touch', 'mobile']) if (v[b] !== undefined && typeof v[b] !== 'boolean') bad(`"${b}" is a boolean`);
        break;
      }
      case 'expectBeside':
        target(v.a, [...sub, 'a'], { keys: true });
        target(v.b, [...sub, 'b'], { keys: true });
        if (!SIDES.includes(v.side)) bad(`"side" is ${SIDES.join(', ')}: where a is relative to b`);
        break;
      case 'switchBrowser':
        if (typeof v !== 'string') bad('the value is the name of a browser');
        else if (!browsers.includes(v)) fail('uiScenario.step-reference', `"${v}" is not one of its browsers (${browsers.length ? browsers.join(', ') : 'it names none'})`);
        else browser = v;
        break;
      case 'setViewport':
        if (!(posInt(v.width) && posInt(v.height))) fail('uiScenario.viewport', 'a viewport needs a positive integer width and height');
        break;
      case 'logScan':
        if (!(Array.isArray(v.forbid) && v.forbid.length)) { bad('it needs a non-empty "forbid" list of patterns'); break; }
        v.forbid.forEach((/** @type {any} */ p, /** @type {number} */ j) => { if (!compiles(p)) fail('uiScenario.pattern', `pattern ${JSON.stringify(p)} is not a regular expression`, [...sub, 'forbid', j]); });
        break;
      case 'expectLog': {
        // A line of the service's log for a logged event, matching the fields given (a subset of what the line
        // holds: its tenant and allowlisted fields). docs/model-and-format.md, "Telemetry".
        timeout();
        if (typeof v.service !== 'string') bad('it needs the "service" whose log is read');
        if (typeof v.event !== 'string') { bad('it needs the "event" (an event id) the line is for'); break; }
        const e = get(v.event, 'event');
        if (!e) { ref('event', `"${v.event}" is not an event`); break; }
        const logging = eventLogging(e);
        if (!logging) { fail('uiScenario.log-event', `event "${e.id}" is not logged (its logging ${e.data.logging === undefined ? 'is not stated' : 'says logged: false'}), so no log line can show it`, [...sub, 'event']); break; }
        if (typeof v.service === 'string' && v.service !== logging.service) fail('uiScenario.log-event', `event "${e.id}" is logged by service "${logging.service}", not "${v.service}"`, [...sub, 'service']);
        if (v.fields === undefined) break;
        if (!isObj(v.fields)) { bad('"fields" maps a member of the line to its expected value'); break; }
        const allowed = [...(logging.tenant !== undefined ? ['tenant'] : []), ...logging.fields.map((f) => f.as)];
        for (const [name, value] of Object.entries(v.fields)) {
          if (!allowed.includes(name)) fail('uiScenario.log-field', `the line of event "${e.id}" holds no member "${name}"; it holds ${allowed.length ? allowed.join(', ') : 'no field of the event'}`, [...sub, 'fields', name]);
          else if (!['string', 'number', 'boolean'].includes(typeof value) && value !== null) bad(`the expected value of "${name}" is a string, a number, a boolean or null`, [...sub, 'fields', name]);
        }
        break;
      }
      case 'waitFor': case 'expectNoEvent':
        if (typeof v.event !== 'string') bad('it needs an "event"');
        else if (!get(v.event, 'event')) ref('event', `"${v.event}" is not an event`);
        if (k === 'expectNoEvent' && v.forMs === undefined) bad('it needs "forMs", how long no such event may arrive');
        timeout(k === 'waitFor' ? 'timeoutMs' : 'forMs');
        break;
      default: break;
    }
  });
}
