// Modal dialogs for the editing operations: create a component, connect two
// components, delete (with a cascade preview), rename an id, and create any
// other entity from the meta-model. All use native <dialog> + showModal().
// Nothing here edits the model except through session.apply.

import { h, on } from './dom.js';
import { entityLabel, inboundRefs } from '../core/query.js';
import { planDelete } from '../core/operations.js';
import metamodel from '../core/metamodel.json' with { type: 'json' };
import { renderDraftFields, showResult, compact } from './property-controls.js';

const ID_RE = new RegExp(metamodel.idPattern);
let dialogUid = 0;

/** Lower-case hyphenated id derived from a display name. @param {string} name */
export function slugify(name) {
  let s = String(name).toLowerCase().replace(/[^a-z0-9_]+/g, '-').replace(/^-+|-+$/g, '');
  if (s && !/^[a-z]/.test(s)) s = `x-${s}`;
  return s;
}

/**
 * Message about an id candidate, or '' when it is fine.
 * @param {any} model @param {string} id @param {string} [self] an id that is allowed to equal the candidate
 */
function idProblem(model, id, self) {
  if (!id) return 'An id is required.';
  if (!ID_RE.test(id)) return 'Use lower-case words joined by hyphens (letters, digits and underscores inside a word; start with a letter).';
  if (id !== self && model.entities.has(id)) return `Id "${id}" is already used by a ${model.entities.get(id).kind}.`;
  return '';
}

/**
 * @param {{title: string, testid: string, submitLabel: string, opener?: Element|null, onSubmit: () => void}} o
 */
function makeDialog(o) {
  const uid = ++dialogUid;
  const opener = o.opener ?? /** @type {HTMLElement|null} */ (document.activeElement);
  const titleId = `dlg-title-${uid}`;
  const body = h('div', { class: 'dialog__body' });
  const err = h('div', { class: 'dialog__error', role: 'alert' });
  err.hidden = true;
  const cancel = h('button', { type: 'button', class: 'btn', 'data-testid': 'dialog-cancel' }, 'Cancel');
  const submit = h('button', { type: 'submit', class: 'btn btn--primary', 'data-testid': o.testid.replace(/-dialog$/, '-submit') }, o.submitLabel);
  const form = h('form', { class: 'dialog__form', novalidate: 'novalidate' },
    h('header', { class: 'dialog__head' }, h('h2', { class: 'dialog__title', id: titleId }, o.title)),
    body, err,
    h('footer', { class: 'dialog__foot' }, cancel, submit));
  const dialog = h('dialog', { class: 'dialog', 'data-testid': o.testid, 'aria-labelledby': titleId }, form);
  const close = () => { if (dialog.open) dialog.close(); };
  on(cancel, 'click', close);
  on(form, 'submit', (/** @type {Event} */ e) => { e.preventDefault(); o.onSubmit(); });
  on(dialog, 'close', () => {
    dialog.remove();
    if (opener && opener.isConnected && typeof (/** @type {any} */ (opener)).focus === 'function') /** @type {any} */ (opener).focus({ preventScroll: true });
  });
  (document.getElementById('dialogs') ?? document.body).append(dialog);
  return {
    dialog, body, submit, close,
    /** @param {any} r */
    fail: (r) => showResult(err, r),
    /** @param {string} message */
    say: (message) => showResult(err, { ok: false, message }),
    clearError: () => showResult(err, { ok: true }),
    show: () => { dialog.showModal(); },
  };
}

/**
 * @param {string} label @param {HTMLElement} control @param {Node|null} [hint]
 * @param {string} [testid]
 */
function field(label, control, hint, testid) {
  if (!control.id) control.id = `dlg-f-${++dialogUid}`;
  return h('div', compact({ class: 'dialog__field', 'data-testid': testid }), h('label', { class: 'dialog__label', for: control.id }, label), h('div', { class: 'dialog__control' }, control, hint ?? null));
}

/** Live id feedback line. */
function idFeedback() {
  const out = h('output', { class: 'dialog__hint dialog__hint--id', 'aria-live': 'polite' });
  return {
    out,
    /** @param {string} problem */
    set(problem) { out.textContent = problem; out.classList.toggle('dialog__hint--bad', !!problem); },
  };
}

// ----------------------------------------------------------------- create ----

/** @param {any} session @param {{parent?: string|null, opener?: Element|null}} [opts] */
export function openCreateDialog(session, opts = {}) {
  const model = session.model;
  const categories = Object.entries(model.meta.categories);
  const subsystems = (model.byKind.component ?? []).filter((/** @type {any} */ c) => c.data.kind === 'subsystem');
  let idEdited = false;

  const name = h('input', { type: 'text', class: 'dialog__input', 'data-testid': 'create-name', autocomplete: 'off' });
  const idIn = h('input', { type: 'text', class: 'dialog__input mono', 'data-testid': 'create-id', autocomplete: 'off', spellcheck: 'false', pattern: metamodel.idPattern });
  const fb = idFeedback();
  const category = h('select', { class: 'dialog__input', 'data-testid': 'create-category' }, categories.map(([k, v]) => h('option', { value: k }, /** @type {any} */ (v).label)));
  const catDesc = h('p', { class: 'dialog__hint' });
  const kind = h('select', { class: 'dialog__input', 'data-testid': 'create-kind' },
    h('option', { value: 'component' }, 'Component'), h('option', { value: 'subsystem' }, 'Subsystem (contains other components)'));
  const parent = h('select', { class: 'dialog__input', 'data-testid': 'create-parent' }, h('option', { value: '' }, '(top level)'),
    subsystems.map((/** @type {any} */ c) => h('option', { value: c.id }, `${entityLabel(c)} (${c.id})`)));
  const purpose = h('textarea', { class: 'dialog__input', rows: '3', 'data-testid': 'create-purpose' });
  if (opts.parent && subsystems.some((/** @type {any} */ c) => c.id === opts.parent)) parent.value = opts.parent;

  const syncCat = () => { catDesc.textContent = model.meta.categories[category.value]?.description ?? ''; };
  const syncId = () => fb.set(idProblem(model, idIn.value));

  const dlg = makeDialog({
    title: 'New component', testid: 'create-dialog', submitLabel: 'Create', opener: opts.opener,
    onSubmit: () => {
      dlg.clearError();
      const id = idIn.value.trim();
      if (!name.value.trim()) { dlg.say('A name is required.'); name.focus({ preventScroll: true }); return; }
      const problem = idProblem(session.model, id);
      if (problem) { dlg.say(problem); idIn.focus({ preventScroll: true }); return; }
      /** @type {Record<string, any>} */
      const data = { id, name: name.value.trim(), category: category.value };
      if (kind.value === 'subsystem') data.kind = 'subsystem';
      if (parent.value) data.parent = parent.value;
      if (purpose.value.trim()) data.purpose = purpose.value.trim();
      const r = session.apply({ type: 'CreateEntity', kind: 'component', data }, { label: `Create component ${id}` });
      if (r.ok) { dlg.close(); session.select(id); } else dlg.fail(r);
    },
  });
  on(name, 'input', () => { if (!idEdited) { idIn.value = slugify(name.value); syncId(); } });
  on(idIn, 'input', () => { idEdited = true; syncId(); });
  on(category, 'change', syncCat);
  dlg.body.append(
    field('Name', name),
    field('Id', idIn, fb.out),
    field('Category', category, catDesc),
    field('Kind', kind),
    field('Parent', parent),
    field('Purpose', purpose));
  syncCat();
  dlg.show();
  name.focus({ preventScroll: true });
  return dlg.dialog;
}

// ---------------------------------------------------------------- connect ----

/** @param {any} session @param {string|null} fromId @param {string|null} toId @param {{opener?: Element|null}} [opts] */
export function openConnectDialog(session, fromId, toId, opts = {}) {
  const model = session.model;
  /** @param {string|null} sel */
  const endpoint = (sel) => {
    const s = h('select', { class: 'dialog__input' }, h('option', { value: '' }, '(choose)'));
    for (const c of model.byKind.component ?? []) {
      s.append(h('option', { value: c.id }, `${entityLabel(c)} (${c.id})`));
      for (const p of model.byKind.port ?? []) if (p.owner === c.id) s.append(h('option', { value: p.id }, `  ↳ port ${entityLabel(p)} (${p.id})`));
    }
    if (sel && model.entities.has(sel)) s.value = sel;
    return s;
  };
  const from = endpoint(fromId);
  from.dataset.testid = 'connect-from';
  const to = endpoint(toId);
  to.dataset.testid = 'connect-to';
  const kinds = Object.entries(model.meta.relationshipKinds);
  const kind = h('select', { class: 'dialog__input', 'data-testid': 'connect-kind' }, kinds.map(([k, v]) => h('option', { value: k }, /** @type {any} */ (v).label)));
  const kindDesc = h('p', { class: 'dialog__hint' });
  const label = h('input', { type: 'text', class: 'dialog__input', 'data-testid': 'connect-label', autocomplete: 'off' });
  const description = h('textarea', { class: 'dialog__input', rows: '2', 'data-testid': 'connect-description' });
  const syncKind = () => {
    const k = model.meta.relationshipKinds[kind.value];
    kindDesc.textContent = k ? `${k.description} ${k.dependency ? 'Counts as a dependency.' : 'Does not count as a dependency.'}` : '';
  };
  const dlg = makeDialog({
    title: 'Connect', testid: 'connect-dialog', submitLabel: 'Connect', opener: opts.opener,
    onSubmit: () => {
      dlg.clearError();
      if (!from.value || !to.value) { dlg.say('Choose both a source and a target.'); return; }
      /** @type {Record<string, any>} */
      const op = { type: 'CreateRelationship', kind: kind.value, from: from.value, to: to.value };
      if (label.value.trim()) op.label = label.value.trim();
      if (description.value.trim()) op.description = description.value.trim();
      const r = session.apply(op, { label: `Connect ${from.value} to ${to.value}` });
      if (r.ok) {
        dlg.close();
        const created = r.affected?.find((/** @type {string} */ id) => session.model.entities.get(id)?.kind === 'relationship');
        if (created) session.select(created);
      } else dlg.fail(r);
    },
  });
  on(kind, 'change', syncKind);
  dlg.body.append(field('From', from), field('To', to), field('Kind', kind, kindDesc), field('Label', label), field('Description', description));
  syncKind();
  dlg.show();
  (fromId ? to : from).focus({ preventScroll: true });
  return dlg.dialog;
}

// ----------------------------------------------------------------- delete ----

/** @param {any} session @param {string} id @param {{opener?: Element|null}} [opts] */
export function openDeleteDialog(session, id, opts = {}) {
  const model = session.model;
  const entity = model.entities.get(id);
  if (!entity) return null;
  const plan = planDelete(model, id);
  const kindLabel = model.meta.entities[entity.kind]?.label ?? entity.kind;
  const hasDependents = plan.dependents.length > 0;
  /** @param {string} eid */
  const name = (eid) => { const e = model.entities.get(eid); return e ? entityLabel(e) : eid; };
  /** @param {string} eid */
  const kindOf = (eid) => model.meta.entities[model.entities.get(eid)?.kind ?? '']?.label ?? model.entities.get(eid)?.kind ?? '';

  /** @type {HTMLInputElement|null} */
  let cascade = null;
  const dlg = makeDialog({
    title: `Delete ${kindLabel.toLowerCase()} "${entityLabel(entity)}"`, testid: 'delete-dialog', submitLabel: 'Delete', opener: opts.opener,
    onSubmit: () => {
      dlg.clearError();
      if (hasDependents && !(cascade && cascade.checked)) { dlg.say('Tick "Also remove or repair these references" to delete.'); return; }
      const r = session.apply({ type: 'DeleteEntity', id, cascade: hasDependents }, { label: `Delete ${entity.kind} ${id}` });
      if (r.ok) {
        dlg.close();
        if (session.selection && plan.entities.includes(session.selection)) session.select(null);
      } else dlg.fail(r);
    },
  });
  dlg.submit.classList.add('btn--danger');

  const others = plan.entities.filter((e) => e !== id);
  dlg.body.append(h('p', { class: 'dialog__text' }, h('code', { class: 'mono' }, id), ` will be removed${others.length ? ` together with ${others.length} nested or dependent ${others.length === 1 ? 'entity' : 'entities'}` : ''}.`));
  if (others.length) {
    dlg.body.append(h('h3', { class: 'dialog__subhead' }, `Removed with it (${others.length})`),
      h('ul', { class: 'dialog__list' }, others.map((o) => h('li', {}, h('span', { class: 'dialog__kind' }, kindOf(o)), ' ', name(o), ' ', h('code', { class: 'mono' }, o)))));
  }
  if (!hasDependents) {
    dlg.body.append(h('p', { class: 'dialog__text' }, 'Nothing else refers to it.'));
  } else {
    dlg.body.append(
      h('h3', { class: 'dialog__subhead' }, `Referenced by (${plan.dependents.length})`),
      h('ul', { class: 'dialog__list' }, plan.dependents.map((d) => {
        const link = h('button', { type: 'button', class: 'btn btn--link', 'data-entity-id': d.id }, `${name(d.id)}`);
        on(link, 'click', () => { dlg.close(); session.select(d.id); });
        return h('li', {}, h('span', { class: 'dialog__kind' }, kindOf(d.id)), ' ', link, ' ', h('code', { class: 'mono' }, d.id), ' through ', h('code', { class: 'mono' }, d.via || '(itself)'));
      })));
    const lines = plan.repairs.map((r) => {
      const from = model.entities.get(r.from);
      const rel = from ? r.path.slice(from.path.length).join('.') : r.path.join('.');
      const what = r.action === 'remove' ? 'removed from list' : r.action === 'unset' ? 'unset' : `moved to parent ${r.value ? name(r.value) : '(top level)'}`;
      return h('li', {}, `${name(r.from)} `, h('code', { class: 'mono' }, r.from), ' — ', h('code', { class: 'mono' }, rel), ': ', what);
    });
    const removedExtra = others.length;
    dlg.body.append(
      h('h3', { class: 'dialog__subhead' }, 'What the cascade does'),
      h('p', { class: 'dialog__text' },
        `${plan.entities.length} ${plan.entities.length === 1 ? 'entity is' : 'entities are'} removed${removedExtra ? ' (listed above and this one)' : ''}; ${plan.repairs.length} ${plan.repairs.length === 1 ? 'reference is' : 'references are'} repaired.`),
      lines.length ? h('ul', { class: 'dialog__list' }, lines) : null);
    cascade = h('input', { type: 'checkbox', class: 'dialog__check', 'data-testid': 'delete-cascade', id: `dlg-cascade-${dialogUid}` });
    const gate = h('label', { class: 'dialog__gate', for: cascade.id }, cascade, 'Also remove or repair these references');
    dlg.body.append(gate);
    dlg.submit.disabled = true;
    on(cascade, 'change', () => { dlg.submit.disabled = !(/** @type {HTMLInputElement} */ (cascade)).checked; });
  }
  dlg.show();
  return dlg.dialog;
}

// ----------------------------------------------------------------- rename ----

/** @param {any} session @param {string} id @param {{opener?: Element|null}} [opts] */
export function openRenameDialog(session, id, opts = {}) {
  const model = session.model;
  const entity = model.entities.get(id);
  if (!entity) return null;
  const refs = inboundRefs(model, id).length;
  const exprs = model.exprs.filter((/** @type {any} */ x) => x.src.includes(id)).length;
  const input = h('input', { type: 'text', class: 'dialog__input mono', 'data-testid': 'rename-id', autocomplete: 'off', spellcheck: 'false', pattern: metamodel.idPattern });
  input.value = id;
  const fb = idFeedback();
  const sync = () => fb.set(input.value === id ? '' : idProblem(session.model, input.value.trim(), id));
  const dlg = makeDialog({
    title: `Rename id of "${entityLabel(entity)}"`, testid: 'rename-dialog', submitLabel: 'Rename', opener: opts.opener,
    onSubmit: () => {
      dlg.clearError();
      const next = input.value.trim();
      if (next === id) { dlg.say('The id is unchanged.'); return; }
      const problem = idProblem(session.model, next, id);
      if (problem) { dlg.say(problem); return; }
      const r = session.apply({ type: 'RenameEntity', id, newId: next }, { label: `Rename ${id} to ${next}` });
      if (r.ok) { dlg.close(); session.select(next); } else dlg.fail(r);
    },
  });
  on(input, 'input', sync);
  dlg.body.append(
    field('Current id', h('code', { class: 'mono dialog__static' }, id)),
    field('New id', input, fb.out),
    h('p', { class: 'dialog__text' }, `${refs} ${refs === 1 ? 'reference' : 'references'} will be rewritten${exprs ? `, and ${exprs} ${exprs === 1 ? 'expression' : 'expressions'} that name it` : ''}. Display names do not change.`));
  dlg.show();
  input.select();
  return dlg.dialog;
}

// ----------------------------------------------------------------- entity ----

/**
 * Create any entity kind from its meta-model definition: the required properties
 * (and the name) as generic controls over an uncommitted draft.
 * With `collect`, the finished declaration is handed to the callback instead of
 * being applied (used for nested entities of a draft that is not committed yet).
 * @param {any} session
 * @param {{kind: string, owner?: string|null, collect?: (data: any) => void, opener?: Element|null}} opts
 */
export function openEntityDialog(session, opts) {
  const model = session.model;
  const kindDef = model.meta.entities[opts.kind];
  if (!kindDef) return null;
  const kindLabel = kindDef.label ?? opts.kind;
  /** @type {Record<string, any>} */
  const defs = {};
  for (const [n, d] of Object.entries(kindDef.properties)) {
    if (n === 'id') continue;
    if (/** @type {any} */ (d).required || n === 'name') defs[n] = d;
  }
  /** @type {Record<string, any>} */
  const draft = {};
  let idEdited = false;
  const hasName = 'name' in defs;
  const idIn = h('input', { type: 'text', class: 'dialog__input mono', 'data-testid': 'entity-id', autocomplete: 'off', spellcheck: 'false', pattern: metamodel.idPattern });
  const fb = idFeedback();
  const syncId = () => fb.set(idProblem(session.model, idIn.value.trim()));

  const dlg = makeDialog({
    title: `New ${kindLabel.toLowerCase()}`, testid: 'entity-dialog', submitLabel: 'Create', opener: opts.opener,
    onSubmit: () => {
      dlg.clearError();
      const id = idIn.value.trim();
      const problem = idProblem(session.model, id);
      if (problem) { dlg.say(problem); idIn.focus({ preventScroll: true }); return; }
      for (const [n, d] of Object.entries(defs)) {
        const v = draft[n];
        if (/** @type {any} */ (d).required && (v === undefined || v === null || v === '' || (Array.isArray(v) && !v.length))) {
          dlg.say(`${/** @type {any} */ (d).label ?? n} is required.`);
          return;
        }
      }
      const data = { id, ...JSON.parse(JSON.stringify(draft)) };
      if (opts.collect) { opts.collect(data); dlg.close(); return; }
      const r = session.apply({ type: 'CreateEntity', kind: opts.kind, ...(opts.owner ? { owner: opts.owner } : {}), data }, { label: `Create ${opts.kind} ${id}` });
      if (r.ok) { dlg.close(); session.select(id); } else dlg.fail(r);
    },
  });
  const fields = h('div', { class: 'dialog__props' });
  renderDraftFields(fields, defs, draft, { session, entity: { id: '', kind: opts.kind }, owner: opts.owner ?? null }, {
    onChange: () => {
      if (!idEdited && hasName && typeof draft.name === 'string') { idIn.value = slugify(draft.name); syncId(); }
    },
  });
  on(idIn, 'input', () => { idEdited = true; syncId(); });
  dlg.body.append(field('Id', idIn, fb.out), fields);
  dlg.show();
  (fields.querySelector('input,select,textarea') ?? idIn).focus({ preventScroll: true });
  return dlg.dialog;
}

