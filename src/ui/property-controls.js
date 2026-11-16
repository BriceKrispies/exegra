// Generic property controls: one control per meta-model property *definition*.
//
// Nothing in this file knows about a particular entity kind. The inspector (and
// the "create entity" dialog) iterate the property definitions of the effective
// meta-model and call renderProperty() for each; a property that a specification
// adds through `vocabulary.properties` therefore gets a working control with no
// code change.
//
// Path convention: `ctx.path` is the path of the *containing* object relative to
// the entity declaration ([] at the top level); the property being rendered lives
// at [...ctx.path, name]. `ctx.commit(fullPath, value)` applies the change and
// returns a TransactionResult-like `{ok, message?, diagnostics?}`; value `null`
// means "remove".

import { h, clear, on } from './dom.js';
import { CLAIM_METHODS } from '../core/claim-methods.js';
import { entityLabel, declarationSite } from '../core/query.js';
import { openRenameDialog, openDeleteDialog, openEntityDialog } from './dialogs.js';

/**
 * @typedef {Object} PropertyContext
 * @property {any} session
 * @property {{id: string, kind: string, data?: any}} entity   entity being edited (or being created)
 * @property {(string|number)[]} path
 * @property {(path: (string|number)[], value: any) => {ok: boolean, message?: string, diagnostics?: any[]}} commit
 * @property {any} [draft]   set when editing a not-yet-committed object
 * @property {string|null} [owner]  owner entity id when the draft is a nested entity
 */

let uid = 0;
const nextId = (/** @type {string} */ p) => `${p}-${++uid}`;

/** Drop attributes whose value would render as a stray "false"/"undefined". @param {Record<string, any>} o */
export function compact(o) {
  return Object.fromEntries(Object.entries(o).filter(([, v]) => v !== undefined && v !== null && v !== false));
}

/** @param {(string|number)[]} p */
export const pathKey = (p) => p.join('.');
const isObj = (/** @type {any} */ v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @template T @param {T} v @returns {T} */
export const cloneJson = (v) => (v === undefined ? v : JSON.parse(JSON.stringify(v)));

/** Set (or, for null/undefined, remove) the value at `path`, creating containers on the way. */
export function setIn(/** @type {any} */ root, /** @type {(string|number)[]} */ path, /** @type {any} */ value) {
  let cur = root;
  for (let i = 0; i < path.length - 1; i++) {
    const k = path[i];
    if (cur[k] === undefined || cur[k] === null || typeof cur[k] !== 'object') cur[k] = typeof path[i + 1] === 'number' ? [] : {};
    cur = cur[k];
  }
  const last = path[path.length - 1];
  if (value === null || value === undefined) { if (Array.isArray(cur)) cur.splice(/** @type {number} */ (last), 1); else delete cur[last]; }
  else cur[last] = value;
}

/** Show a rejected result under a control. @param {HTMLElement} err @param {any} r */
export function showResult(err, r) {
  clear(err);
  if (!r || r.ok !== false) { err.hidden = true; return; }
  err.hidden = false;
  err.append(h('div', { class: 'prop__error-msg' }, r.message ?? 'The change was rejected.'));
  const ds = /** @type {any[]} */ (r.diagnostics ?? []);
  const errs = ds.filter((d) => d.severity === 'error');
  for (const d of (errs.length ? errs : ds).slice(0, 3)) err.append(h('div', { class: 'prop__error-diag' }, d.loc ? h('span', { class: 'mono' }, `${d.loc.line}:${d.loc.column} `) : null, d.message));
}

/** @param {any} def */
function isComposite(def) { return def.type === 'list' || def.type === 'object' || def.type === 'entities'; }
/** Types whose value is a JSON document edited as text. @param {any} def */
const isJson = (def) => ['map', 'effect', 'evaluation', 'any'].includes(def.type);

/**
 * Render one property.
 * @param {any} def property definition from the meta-model
 * @param {string|number} name property name (or list index)
 * @param {any} value current value (undefined when unset)
 * @param {PropertyContext} ctx
 * @returns {HTMLElement}
 */
export function renderProperty(def, name, value, ctx) {
  const path = [...ctx.path, name];
  const key = pathKey(path);
  const labelText = def.label ?? (typeof name === 'number' ? `Item ${name + 1}` : name);
  const err = h('div', { class: 'prop__error', role: 'alert' });
  err.hidden = true;
  const fx = {
    path,
    err,
    /** @param {any} v */
    commit(v) {
      const r = ctx.commit(path, v);
      showResult(err, r);
      return r.ok !== false;
    },
  };
  const id = nextId('prop');
  const docId = id + '-doc';
  const control = buildControl(def, value, fx, ctx, id);
  const req = def.required ? h('span', { class: 'prop__req', title: 'Required' }, '*', h('span', { class: 'sr-only' }, ' (required)')) : null;
  const ext = def.extension ? h('span', { class: 'chip chip--model', title: 'Defined by this specification\'s vocabulary, not by the built-in meta-model' }, 'model-defined') : null;
  const doc = def.doc ? h('p', { class: 'prop__doc', id: docId }, def.doc) : null;
  const classes = ['prop', def.required ? 'prop--required' : '', def.extension ? 'prop--extension' : '', isComposite(def) ? 'prop--group' : ''].filter(Boolean).join(' ');
  if (isComposite(def)) {
    return h('fieldset', { class: classes, 'data-prop': key }, h('legend', { class: 'prop__legend' }, labelText, req, ext), doc, control, err);
  }
  const target = control.id === id ? control : control.querySelector(`[id="${id}"]`);
  if (target && doc) target.setAttribute('aria-describedby', docId);
  return h('div', { class: classes, 'data-prop': key }, h('label', { class: 'prop__label', for: id }, labelText, req, ext), h('div', { class: 'prop__body' }, control, doc, err));
}

/**
 * @param {any} def @param {any} value
 * @param {{path: (string|number)[], err: HTMLElement, commit: (v: any) => boolean}} fx
 * @param {PropertyContext} ctx @param {string} id
 * @returns {HTMLElement}
 */
function buildControl(def, value, fx, ctx, id) {
  switch (def.type) {
    case 'id': return idControl(ctx, id);
    case 'list': return listControl(def, value, fx, ctx, id);
    case 'object': return objectControl(def, value, fx, ctx);
    case 'entities': return entitiesControl(def, value, fx, ctx);
    default: return scalarControl(def, value, fx, ctx, id);
  }
}

/** @param {any} def @param {any} value @param {any} fx @param {PropertyContext} ctx @param {string} id @param {{rows?: number, placeholder?: string}} [o] */
function scalarControl(def, value, fx, ctx, id, o = {}) {
  switch (def.type) {
    case 'string': return textInput(value, fx, id, false, o);
    case 'expr': return textInput(value, fx, id, true, o);
    case 'text': return textArea(value, fx, id, o.rows ?? 2, o);
    case 'boolean': return checkbox(value, fx, id);
    case 'number': return numberInput(value, fx, id, o);
    case 'enum': return enumSelect(def, value, fx, ctx, id);
    case 'ref': return refControl(def, value, fx, ctx, id);
    default:
      if (isJson(def)) return jsonControl(def, value, fx, id, ctx);
      return h('span', { class: 'prop__unsupported mono', id }, `Unsupported property type "${def.type}"`);
  }
}

// ---------------------------------------------------------------- id ----

/** @param {PropertyContext} ctx @param {string} id */
function idControl(ctx, id) {
  return h('div', { class: 'prop__idrow', id },
    h('code', { class: 'mono prop__id' }, ctx.entity.id),
    h('button', { type: 'button', class: 'btn btn--small', onclick: () => openRenameDialog(ctx.session, ctx.entity.id) }, 'Rename id'));
}

// ------------------------------------------------------------ scalars ----

/** @param {any} value @param {any} fx @param {string} id @param {boolean} mono @param {{placeholder?: string}} o */
function textInput(value, fx, id, mono, o) {
  let orig = value === undefined || value === null ? '' : String(value);
  const input = h('input', compact({ type: 'text', id, class: 'prop__input' + (mono ? ' mono' : ''), autocomplete: 'off', spellcheck: 'false', placeholder: o.placeholder }));
  input.value = orig;
  on(input, 'change', () => {
    const v = input.value;
    if (v === orig) return;
    if (fx.commit(v === '' ? null : v)) orig = v; else input.value = orig;
  });
  on(input, 'keydown', (/** @type {KeyboardEvent} */ e) => { if (e.key === 'Escape' && input.value !== orig) { input.value = orig; e.stopPropagation(); } });
  return input;
}

/** @param {any} value @param {any} fx @param {string} id @param {number} rows @param {{placeholder?: string}} o */
function textArea(value, fx, id, rows, o) {
  let orig = value === undefined || value === null ? '' : String(value);
  const ta = h('textarea', compact({ id, class: 'prop__input prop__textarea', rows: String(rows), placeholder: o.placeholder }));
  ta.value = orig;
  const grow = () => { ta.style.height = 'auto'; ta.style.height = `${Math.max(ta.scrollHeight, 0)}px`; };
  const submit = () => {
    const v = ta.value;
    if (v === orig) return;
    if (fx.commit(v === '' ? null : v)) orig = v; else { ta.value = orig; grow(); }
  };
  on(ta, 'input', grow);
  on(ta, 'blur', submit);
  on(ta, 'keydown', (/** @type {KeyboardEvent} */ e) => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); submit(); }
    else if (e.key === 'Escape' && ta.value !== orig) { ta.value = orig; grow(); e.stopPropagation(); }
  });
  requestAnimationFrame(grow);
  return ta;
}

/** @param {any} value @param {any} fx @param {string} id */
function checkbox(value, fx, id) {
  const box = h('input', { type: 'checkbox', id, class: 'prop__check' });
  box.checked = value === true;
  on(box, 'change', () => { if (!fx.commit(box.checked)) box.checked = value === true; });
  return box;
}

/** @param {any} value @param {any} fx @param {string} id @param {{placeholder?: string}} o */
function numberInput(value, fx, id, o) {
  const orig = typeof value === 'number' ? String(value) : '';
  const input = h('input', compact({ type: 'number', id, step: 'any', class: 'prop__input prop__input--number mono', placeholder: o.placeholder }));
  input.value = orig;
  on(input, 'change', () => {
    if (input.value === orig) return;
    const v = input.value === '' ? null : input.valueAsNumber;
    if (v !== null && !Number.isFinite(v)) { input.value = orig; return; }
    if (!fx.commit(v)) input.value = orig;
  });
  on(input, 'keydown', (/** @type {KeyboardEvent} */ e) => { if (e.key === 'Escape' && input.value !== orig) { input.value = orig; e.stopPropagation(); } });
  return input;
}

/** @param {any} def @param {PropertyContext} ctx @returns {{value: string, label: string, title?: string}[]} */
function enumOptions(def, ctx) {
  const meta = ctx.session.model.meta;
  if (Array.isArray(def.values)) return def.values.map((/** @type {string} */ v) => ({ value: v, label: v }));
  if (def.valuesFrom === 'projections') return (meta.projections ?? []).map((/** @type {string} */ v) => ({ value: v, label: v }));
  if (def.valuesFrom && isObj(meta[def.valuesFrom])) {
    return Object.entries(meta[def.valuesFrom]).map(([k, v]) => ({ value: k, label: /** @type {any} */ (v)?.label ?? k, title: /** @type {any} */ (v)?.description }));
  }
  return [];
}

/** @param {any} def @param {any} value @param {any} fx @param {PropertyContext} ctx @param {string} id */
function enumSelect(def, value, fx, ctx, id) {
  const sel = h('select', { id, class: 'prop__input' });
  const opts = enumOptions(def, ctx);
  if (!def.required) sel.append(h('option', { value: '' }, '(unset)'));
  for (const o of opts) sel.append(h('option', compact({ value: o.value, title: o.title }), o.label));
  if (typeof value === 'string' && !opts.some((o) => o.value === value)) sel.append(h('option', { value }, `${value} (not defined)`));
  const orig = typeof value === 'string' ? value : '';
  sel.value = orig;
  if (orig === '' && def.required && opts.length) sel.selectedIndex = -1;
  on(sel, 'change', () => { if (!fx.commit(sel.value === '' ? null : sel.value)) { sel.value = orig; if (orig === '' && def.required) sel.selectedIndex = -1; } });
  return sel;
}

/** @param {any} def @param {PropertyContext} ctx */
function refCandidates(def, ctx) {
  const model = ctx.session.model;
  /** @type {any[]} */
  const out = [];
  const kinds = (def.ref ?? []).includes('*') ? Object.keys(model.byKind) : (def.ref ?? []);
  for (const k of kinds) for (const e of model.byKind[k] ?? []) if (e.id !== ctx.entity.id) out.push(e);
  return out;
}

/** @param {any} model @param {any} e */
function refLabel(model, e) {
  const label = entityLabel(e);
  let s = label === e.id ? e.id : `${label} (${e.id})`;
  if (e.owner) { const o = model.entities.get(e.owner); if (o) s += ` — ${entityLabel(o)}`; }
  return s;
}

/** All ids declared inside a draft object, at any depth. @param {any} v @param {string[]} [out] */
function draftIds(v, out = []) {
  if (Array.isArray(v)) v.forEach((x) => draftIds(x, out));
  else if (isObj(v)) { if (typeof v.id === 'string') out.push(v.id); for (const x of Object.values(v)) draftIds(x, out); }
  return out;
}

/** @param {any} def @param {any} value @param {any} fx @param {PropertyContext} ctx @param {string} id */
function refControl(def, value, fx, ctx, id) {
  const session = ctx.session;
  const model = session.model;
  const orig = typeof value === 'string' ? value : '';
  const nestedTarget = (def.ref ?? []).some((/** @type {string} */ k) => k !== '*' && declarationSite(model, k)?.ownerKind);
  /** @type {HTMLElement} */
  let field;
  if (ctx.draft && nestedTarget) {
    // The targets may be declared in the same draft (a behavior's initial state): free text with suggestions.
    const listId = id + '-list';
    const known = refCandidates(def, ctx).filter((e) => !ctx.owner || e.owner === ctx.owner).map((e) => e.id);
    const ids = [...new Set([...draftIds(ctx.draft), ...known])];
    const input = h('input', { type: 'text', id, class: 'prop__input mono', list: listId, autocomplete: 'off', spellcheck: 'false' });
    input.value = orig;
    const dl = h('datalist', { id: listId }, ids.map((x) => h('option', { value: x })));
    on(input, 'change', () => { if (!fx.commit(input.value.trim() === '' ? null : input.value.trim())) input.value = orig; });
    field = h('span', { class: 'prop__refwrap' }, input, dl);
  } else {
    const sel = h('select', { id, class: 'prop__input' });
    if (!def.required) sel.append(h('option', { value: '' }, '(none)'));
    const cands = refCandidates(def, ctx);
    for (const e of cands) sel.append(h('option', { value: e.id }, refLabel(model, e)));
    const literals = Array.isArray(def.literals) ? def.literals : [];
    for (const lit of literals) sel.append(h('option', { value: lit }, lit));
    if (orig && !literals.includes(orig) && !cands.some((e) => e.id === orig)) sel.append(h('option', { value: orig }, `${orig} (missing)`));
    sel.value = orig;
    if (orig === '' && def.required) sel.selectedIndex = -1;
    on(sel, 'change', () => {
      const ok = fx.commit(sel.value === '' ? null : sel.value);
      if (!ok) { sel.value = orig; if (orig === '' && def.required) sel.selectedIndex = -1; }
      go.disabled = !sel.value || !model.entities.has(sel.value);
    });
    const go = h('button', { type: 'button', class: 'btn btn--small btn--icon', 'aria-label': 'Select the referenced entity', title: 'Select the referenced entity' }, 'go');
    go.disabled = !orig || !model.entities.has(orig);
    on(go, 'click', () => { if (sel.value) session.select(sel.value); });
    field = h('span', { class: 'prop__refwrap' }, sel, go);
  }
  return field;
}

// --------------------------------------------------------------- JSON ----

/** @param {any} def @param {any} value @param {any} fx @param {string} id @param {any} ctx */
function jsonControl(def, value, fx, id, ctx) {
  const text = (/** @type {any} */ v) => (v === undefined ? '' : JSON.stringify(v, null, 2));
  let orig = text(value);
  const ta = h('textarea', { id, class: 'prop__input prop__textarea mono', rows: String(Math.min(12, Math.max(2, orig.split('\n').length))), spellcheck: 'false', wrap: 'off', placeholder: 'JSON' });
  ta.value = orig;
  const local = h('div', { class: 'prop__error', role: 'alert' });
  local.hidden = true;
  const docBox = def.type === 'evaluation' ? h('div', { class: 'prop__method' }) : null;
  const fillDoc = () => {
    if (!docBox) return;
    clear(docBox);
    /** @type {any} */
    let parsed;
    try { parsed = ta.value.trim() ? JSON.parse(ta.value) : undefined; } catch { parsed = undefined; }
    if (!isObj(parsed) || typeof parsed.method !== 'string') return;
    const external = ctx.session.model?.meta.verificationMethods;
    if (external && Object.hasOwn(external, parsed.method)) {
      const x = external[parsed.method];
      docBox.append(h('p', { class: 'prop__method-doc' }, h('code', { class: 'mono' }, parsed.method), ` — ${x.label}. `, x.description ?? '',
        ' This verification is carried out outside Exegra; the claim\'s status comes only from recorded evidence.'));
      return;
    }
    const m = Object.hasOwn(CLAIM_METHODS, parsed.method) ? /** @type {Record<string, any>} */ (CLAIM_METHODS)[parsed.method] : undefined;
    if (!m) { docBox.append(h('p', { class: 'prop__method-unsupported' }, 'This method is not supported by this build; the claim cannot be evaluated.')); return; }
    docBox.append(h('p', { class: 'prop__method-doc' }, h('code', { class: 'mono' }, parsed.method), ' — ', m.doc));
    const params = Object.entries(m.params ?? {});
    if (params.length) {
      docBox.append(h('dl', { class: 'prop__params' }, params.map(([n, p]) => [
        h('dt', { class: 'mono' }, n, /** @type {any} */ (p).required ? h('span', { class: 'prop__req', title: 'Required' }, '*') : null),
        h('dd', {}, h('span', { class: 'mono' }, /** @type {any} */ (p).type), /** @type {any} */ (p).doc ? ` — ${/** @type {any} */ (p).doc}` : ''),
      ])));
    }
  };
  fillDoc();
  const submit = () => {
    const raw = ta.value;
    if (raw === orig) { local.hidden = true; return; }
    /** @type {any} */
    let parsed = null;
    if (raw.trim() !== '') {
      try { parsed = JSON.parse(raw); } catch (e) {
        local.hidden = false;
        clear(local);
        local.append(h('div', { class: 'prop__error-msg' }, `Not valid JSON: ${/** @type {Error} */ (e).message}`));
        return;
      }
    }
    local.hidden = true;
    if (fx.commit(parsed)) orig = raw; else { ta.value = orig; fillDoc(); }
  };
  on(ta, 'input', () => { fillDoc(); local.hidden = true; });
  on(ta, 'blur', submit);
  on(ta, 'keydown', (/** @type {KeyboardEvent} */ e) => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); submit(); }
    else if (e.key === 'Escape' && ta.value !== orig) { ta.value = orig; fillDoc(); local.hidden = true; e.stopPropagation(); }
  });
  return h('div', { class: 'prop__json', id: id + '-wrap' }, ta, local, docBox);
}

// ------------------------------------------------------------- groups ----

/** @param {any} def @param {any} value @param {any} fx @param {PropertyContext} ctx */
function objectControl(def, value, fx, ctx) {
  const fields = def.fields ?? {};
  const wrap = h('div', { class: 'prop__fields' });
  const sub = { ...ctx, path: fx.path };
  const obj = isObj(value) ? value : {};
  for (const [n, d] of Object.entries(fields)) wrap.append(renderProperty(/** @type {any} */ (d), n, obj[n], sub));
  return wrap;
}

/** Item control for lists. @param {any} def list definition */
function listControl(def, value, fx, ctx, id) {
  const items = def.items ?? { type: 'string' };
  const arr = Array.isArray(value) ? value : [];
  const wrap = h('div', { class: 'prop__list', id });
  const list = h('ul', { class: 'prop__items' });
  wrap.append(list);

  if (items.type === 'object') {
    arr.forEach((item, i) => {
      const itemPath = [...fx.path, i];
      /** Edits inside item i rewrite the whole array. */
      const sub = {
        ...ctx,
        path: itemPath,
        /** @param {(string|number)[]} p @param {any} v */
        commit: (p, v) => {
          const next = cloneJson(arr);
          setIn(next, p.slice(fx.path.length), v);
          return ctx.commit(fx.path, next);
        },
      };
      const body = h('div', { class: 'prop__fields' });
      for (const [n, d] of Object.entries(items.fields ?? {})) body.append(renderProperty(/** @type {any} */ (d), n, isObj(item) ? item[n] : undefined, sub));
      const remove = h('button', { type: 'button', class: 'btn btn--small', 'aria-label': `Remove ${def.label ?? 'item'} ${i + 1}` }, 'Remove');
      on(remove, 'click', () => { const next = cloneJson(arr); next.splice(i, 1); fx.commit(next.length ? next : null); });
      list.append(h('li', { class: 'prop__item prop__item--object', 'data-prop': pathKey(itemPath) }, h('div', { class: 'prop__itemhead' }, h('span', { class: 'prop__itemno' }, `#${i + 1}`), remove), body));
    });
    wrap.append(pendingObjectAdder(def, items, arr, fx, ctx));
    return wrap;
  }

  arr.forEach((item, i) => {
    const itemId = nextId('item');
    const itemFx = {
      path: [...fx.path, i],
      err: fx.err,
      /** @param {any} v */
      commit(v) {
        const next = cloneJson(arr);
        if (v === null) next.splice(i, 1); else next[i] = v;
        return fx.commit(next.length ? next : null);
      },
    };
    const control = scalarControl(items, item, itemFx, ctx, itemId, { rows: 1 });
    control.setAttribute('aria-label', `${def.label ?? 'Item'} ${i + 1}`);
    const remove = h('button', { type: 'button', class: 'btn btn--small btn--icon', 'aria-label': `Remove ${def.label ?? 'item'} ${i + 1}`, title: 'Remove' }, '×');
    on(remove, 'click', () => { const next = cloneJson(arr); next.splice(i, 1); fx.commit(next.length ? next : null); });
    list.append(h('li', { class: 'prop__item', 'data-prop': pathKey([...fx.path, i]) }, control, remove));
  });

  // "Add" row.
  const addFx = {
    path: [...fx.path, arr.length],
    err: fx.err,
    /** @param {any} v */
    commit(v) { return v === null ? true : fx.commit([...cloneJson(arr), v]); },
  };
  const addLabel = `Add ${(def.label ?? 'item').toLowerCase()}`;
  let addRow;
  if (items.type === 'ref' || items.type === 'enum') {
    const ctl = scalarControl(items, undefined, addFx, ctx, nextId('add'));
    const sel = ctl.tagName === 'SELECT' ? ctl : ctl.querySelector('select');
    if (sel) {
      // Choosing a value adds it; the empty entry is the placeholder.
      if (!sel.querySelector('option[value=""]')) sel.insertBefore(h('option', { value: '' }, `${addLabel}…`), sel.firstChild);
      else sel.querySelector('option[value=""]').textContent = `${addLabel}…`;
      sel.value = '';
      sel.setAttribute('aria-label', addLabel);
    }
    addRow = h('div', { class: 'prop__add' }, ctl);
  } else {
    const input = h('input', { type: items.type === 'number' ? 'number' : 'text', class: 'prop__input' + (items.type === 'number' ? ' mono' : ''), placeholder: `${addLabel}…`, 'aria-label': addLabel });
    const btn = h('button', { type: 'button', class: 'btn btn--small' }, 'Add');
    const add = () => {
      const raw = input.value.trim();
      if (raw === '') return;
      const v = items.type === 'number' ? Number(raw) : raw;
      if (items.type === 'number' && !Number.isFinite(v)) return;
      if (addFx.commit(v)) input.value = '';
    };
    on(btn, 'click', add);
    on(input, 'keydown', (/** @type {KeyboardEvent} */ e) => { if (e.key === 'Enter') { e.preventDefault(); add(); } });
    addRow = h('div', { class: 'prop__add' }, input, btn);
  }
  wrap.append(addRow);
  return wrap;
}

/** "Add" for lists of objects: a small pending editor whose value is committed whole. */
function pendingObjectAdder(def, items, arr, fx, ctx) {
  const box = h('div', { class: 'prop__pending' });
  const open = h('button', { type: 'button', class: 'btn btn--small' }, `Add ${(def.label ?? 'item').toLowerCase()}`);
  box.append(open);
  on(open, 'click', () => {
    clear(box);
    const draft = {};
    const fields = h('div', { class: 'prop__fields' });
    const base = { session: ctx.session, entity: ctx.entity, owner: ctx.owner ?? null };
    renderDraftFields(fields, items.fields ?? {}, draft, base, { skip: [] });
    const add = h('button', { type: 'button', class: 'btn btn--small btn--primary' }, 'Add');
    const cancel = h('button', { type: 'button', class: 'btn btn--small' }, 'Cancel');
    on(add, 'click', () => { fx.commit([...cloneJson(arr), cloneJson(draft)]); });
    on(cancel, 'click', () => { clear(box); box.append(open); });
    box.append(h('div', { class: 'prop__item prop__item--pending' }, fields, h('div', { class: 'prop__actions' }, add, cancel)));
    box.querySelector('input,select,textarea')?.focus({ preventScroll: true });
  });
  return box;
}

/** @param {any} def @param {any} value @param {any} fx @param {PropertyContext} ctx */
function entitiesControl(def, value, fx, ctx) {
  const session = ctx.session;
  const model = session.model;
  const kindDef = model.meta.entities[def.entity];
  const kindLabel = kindDef?.label ?? def.entity;
  const wrap = h('div', { class: 'prop__entities' });
  const list = h('ul', { class: 'prop__items' });
  wrap.append(list);
  if (ctx.draft) {
    const arr = Array.isArray(value) ? value : [];
    arr.forEach((d, i) => {
      const remove = h('button', { type: 'button', class: 'btn btn--small btn--icon', 'aria-label': `Remove ${kindLabel} ${d?.id ?? i + 1}`, title: 'Remove' }, '×');
      on(remove, 'click', () => { const next = cloneJson(arr); next.splice(i, 1); fx.commit(next.length ? next : null); });
      list.append(h('li', { class: 'prop__item prop__item--entity' }, h('span', { class: 'prop__entlabel' }, d?.name ?? d?.id ?? ''), h('code', { class: 'mono' }, d?.id ?? ''), remove));
    });
    const add = h('button', { type: 'button', class: 'btn btn--small' }, `Add ${kindLabel}`);
    on(add, 'click', () => openEntityDialog(session, { kind: def.entity, owner: null, collect: (/** @type {any} */ data) => { fx.commit([...cloneJson(arr), data]); }, opener: add }));
    wrap.append(h('div', { class: 'prop__add' }, add));
    return wrap;
  }
  const rows = [...model.entities.values()].filter((e) => e.owner === ctx.entity.id && e.kind === def.entity).sort((a, b) => a.loc.offset - b.loc.offset);
  for (const e of rows) {
    const select = h('button', { type: 'button', class: 'btn btn--link prop__entlabel', 'data-entity-id': e.id, title: `Select ${e.id}` }, entityLabel(e));
    on(select, 'click', () => session.select(e.id));
    const remove = h('button', { type: 'button', class: 'btn btn--small btn--icon', 'aria-label': `Remove ${kindLabel} ${e.id}`, title: 'Remove' }, '×');
    on(remove, 'click', () => openDeleteDialog(session, e.id, { opener: remove }));
    list.append(h('li', { class: 'prop__item prop__item--entity', 'data-prop': pathKey([...fx.path, e.id]) }, select, h('code', { class: 'mono' }, e.id), remove));
  }
  const add = h('button', { type: 'button', class: 'btn btn--small' }, `Add ${kindLabel}`);
  on(add, 'click', () => openEntityDialog(session, { kind: def.entity, owner: ctx.entity.id, opener: add }));
  wrap.append(h('div', { class: 'prop__add' }, add));
  return wrap;
}

// ------------------------------------------------------------- drafts ----

/**
 * Render (and keep re-rendering) the controls of a not-yet-committed object into
 * `container`. Edits mutate `draft`; nothing touches the model.
 * @param {HTMLElement} container
 * @param {Record<string, any>} defs property definitions
 * @param {any} draft the object being built
 * @param {{session: any, entity: {id: string, kind: string}, owner?: string|null}} base
 * @param {{skip?: string[], onChange?: (draft: any) => void}} [opts]
 * @returns {() => void} re-render function
 */
export function renderDraftFields(container, defs, draft, base, opts = {}) {
  const skip = opts.skip ?? [];
  const render = () => {
    const active = document.activeElement;
    const focusKey = active && container.contains(active) ? /** @type {HTMLElement|null} */ (active.closest('[data-prop]'))?.dataset.prop : null;
    clear(container);
    /** @type {PropertyContext} */
    const ctx = {
      ...base,
      draft,
      path: [],
      commit(p, v) {
        setIn(draft, p, v);
        opts.onChange?.(draft);
        setTimeout(render, 0);
        return { ok: true };
      },
    };
    for (const [name, def] of Object.entries(defs)) {
      if (skip.includes(name)) continue;
      container.append(renderProperty(def, name, draft[name], ctx));
    }
    if (focusKey) {
      const wrapper = [...container.querySelectorAll('[data-prop]')].find((n) => /** @type {HTMLElement} */ (n).dataset.prop === focusKey);
      /** @type {HTMLElement|null|undefined} */ (wrapper?.querySelector('input,select,textarea'))?.focus({ preventScroll: true });
    }
  };
  render();
  return render;
}
