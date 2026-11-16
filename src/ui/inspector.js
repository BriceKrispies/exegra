// The semantic inspector. The property editor is generated from the effective
// meta-model (property-controls.js); the other sections are read-only queries
// over the model and the claim results, each entry a link to the entity it names.

import { h, clear, on } from './dom.js';
import { entityLabel, relationshipsOf, dependencies, contractsOf, childrenOf, ancestorsOf, inboundRefs, componentOf } from '../core/query.js';
import { CLAIM_STATUSES } from '../core/claim-methods.js';
import { recordFields, copiesOf, copyFields, sourcesOf, isPrincipalData, PRINCIPAL } from '../core/data-model.js';
import { renderProperty, pathKey } from './property-controls.js';
import { openDeleteDialog, openConnectDialog, openCreateDialog, openRenameDialog } from './dialogs.js';

const ILLUSTRATIVE = 'Illustrative example — not a statement about real software.';

/** @param {string} s */
const sentence = (s) => (s ? s.charAt(0).toUpperCase() + s.slice(1).replace(/-/g, ' ') : s);

/**
 * @param {HTMLElement} el
 * @param {any} session
 * @returns {() => void} unmount
 */
export function mountInspector(el, session) {
  const root = h('div', { class: 'inspector', 'data-testid': 'inspector' });
  clear(el);
  el.append(root);
  /** @type {string|null} */
  let lastId = null;
  let pending = 0;

  // ---- small builders ----------------------------------------------------

  /** @param {string} kind */
  const kindLabel = (kind) => session.model?.meta.entities[kind]?.label ?? kind;

  /** A button that selects an entity. @param {string} id @param {string} [text] */
  function link(id, text) {
    const e = session.model.entities.get(id);
    if (!e) return h('span', { class: 'ilink ilink--missing mono', title: 'No such entity' }, `${text ?? id} (missing)`);
    const b = h('button', { type: 'button', class: 'ilink', 'data-entity-id': id, title: `${kindLabel(e.kind)} ${id}` }, text ?? entityLabel(e));
    on(b, 'click', () => session.select(id));
    return b;
  }

  /** @param {string} text @param {string} [tone] none|ok|ok-external|bad|warn */
  function chip(text, tone) {
    return h('span', { class: 'chip', 'data-tone': tone ?? 'none' }, h('span', { class: 'chip__dot', 'aria-hidden': 'true' }), text);
  }

  /** A claim status chip. The tone comes only from CLAIM_STATUSES. @param {string} status @param {boolean} [full] */
  function statusChip(status, full) {
    const s = /** @type {Record<string, {label: string, tone: string}>} */ (CLAIM_STATUSES)[status];
    return chip(full && s ? s.label : sentence(status), s?.tone ?? 'none');
  }

  /** @param {string} name @param {string} title @param {any[]} children @param {string} [extra] */
  function section(name, title, children, extra) {
    return h('section', { class: 'isec' + (extra ? ` isec--${extra}` : ''), 'data-section': name, 'aria-labelledby': `isec-${name}` },
      h('h3', { class: 'isec__head', id: `isec-${name}` }, title), ...children);
  }

  /** @param {any[]} rows rows of [label, ...content] */
  function kv(rows) {
    return h('dl', { class: 'kv' }, rows.filter(Boolean).map(([label, ...content]) => h('div', { class: 'kv__row' }, h('dt', { class: 'kv__k' }, label), h('dd', { class: 'kv__v' }, ...content))));
  }

  /** @param {any[]} items */
  const ul = (items) => h('ul', { class: 'ilist' }, items.map((i) => h('li', { class: 'ilist__item' }, i)));

  /** @param {string} id */
  function entityRef(id) {
    return [link(id), ' ', h('code', { class: 'mono ilist__id' }, id)];
  }

  // ---- sections ----------------------------------------------------------

  /** @param {any} entity */
  function identity(entity) {
    const model = session.model;
    const rows = [
      typeof entity.data?.ref === 'string' && entity.data.ref ? ['Reference', h('code', { class: 'mono', 'data-testid': 'identity-reference' }, entity.data.ref)] : null,
      ['Kind', kindLabel(entity.kind)],
      ['Label', h('strong', { class: 'insp__title' }, entityLabel(entity))],
      ['Id', h('span', null, h('code', { class: 'mono' }, entity.id), ' ',
        h('button', { type: 'button', class: 'btn btn--small', 'data-testid': 'rename-id-open', title: 'Change the stable id and rewrite every reference to it', onclick: () => openRenameDialog(session, entity.id) }, 'Rename id'))],
    ];
    if (entity.owner) rows.push(['Part of', link(entity.owner)]);
    if (entity.kind === 'component') {
      const anc = ancestorsOf(model, entity.id).reverse();
      if (anc.length) {
        const nav = h('nav', { class: 'crumbs', 'aria-label': 'Containing subsystems' });
        anc.forEach((a, i) => { if (i) nav.append(h('span', { class: 'crumbs__sep', 'aria-hidden': 'true' }, '›')); nav.append(link(a)); });
        rows.push(['Inside', nav]);
      }
    }
    const src = h('button', { type: 'button', class: 'ilink mono', 'data-testid': 'reveal-source', title: 'Show this declaration in the source editor' }, `spec.jsonc:${entity.loc.line}:${entity.loc.column}`);
    on(src, 'click', () => session.revealSource(entity.id));
    rows.push(['Source', src]);
    if (typeof entity.data?.source === 'string' && entity.data.source) rows.push(['Origin', h('code', { class: 'mono', 'data-testid': 'identity-origin' }, entity.data.source)]);
    const illustrative = entity.data?.illustrative === true || model.system?.data?.illustrative === true;
    return section('identity', 'Identity', [
      illustrative ? h('p', { class: 'insp__illustrative', 'data-testid': 'illustrative-notice' }, ILLUSTRATIVE) : null,
      kv(rows),
    ]);
  }

  /** @param {any} entity */
  function properties(entity) {
    const model = session.model;
    const defs = model.meta.entities[entity.kind]?.properties ?? {};
    const ctx = {
      session,
      entity,
      path: /** @type {(string|number)[]} */ ([]),
      /** @param {(string|number)[]} path @param {any} value */
      commit: (path, value) => session.apply({ type: 'SetProperty', id: entity.id, property: path, value }, { label: `Set ${pathKey(path)} of ${entity.id}` }),
    };
    const body = h('div', { class: 'props', 'data-testid': 'properties' });
    for (const [name, def] of Object.entries(defs)) {
      if (name === 'id') continue;
      body.append(renderProperty(/** @type {any} */ (def), name, entity.data[name], ctx));
    }
    return section('properties', 'Properties', [body]);
  }

  /** @param {any} entity */
  function diagnosticsSection(entity) {
    const ds = (session.diagnostics ?? []).filter((/** @type {any} */ d) => d.entityId === entity.id);
    if (!ds.length) return null;
    return section('diagnostics', 'Diagnostics', [ul(ds.slice(0, 8).map((/** @type {any} */ d) => [chip(d.severity === 'info' ? 'gap' : d.severity, d.severity === 'error' ? 'bad' : d.severity === 'warning' ? 'warn' : 'none'), ' ', d.message]))]);
  }

  /** @param {any} c */
  function componentSections(c) {
    const model = session.model;
    const out = [];
    const rels = relationshipsOf(model, c.id);
    if (rels.length) {
      out.push(section('relationships', 'Relationships', [ul(rels.map(({ relationship, direction, other, viaPort }) => {
        const kind = model.meta.relationshipKinds[relationship.data.kind];
        return [
          h('span', { class: 'rel__arrow', title: direction === 'out' ? 'outgoing' : 'incoming', 'aria-label': direction === 'out' ? 'outgoing' : 'incoming' }, direction === 'out' ? '→' : '←'),
          ' ', h('span', { class: 'rel__kind', title: kind?.description ?? '' }, kind?.label ?? relationship.data.kind),
          ' ', other ? link(other.id) : h('span', { class: 'ilink ilink--missing' }, '(unresolved)'),
          viaPort ? [' via port ', link(viaPort)] : null,
          ' ', h('span', { class: 'ilist__sub' }, link(relationship.id, relationship.id)),
        ];
      }))]));
    }
    const deps = dependencies(model, c.id, { transitive: true });
    const dependents = dependencies(model, c.id, { transitive: true, direction: 'in' });
    if (deps.length || dependents.length) {
      const depList = (/** @type {any[]} */ list) => ul(list.map((d) => [h('span', { class: 'dep__depth mono', title: `${d.depth} hop${d.depth === 1 ? '' : 's'}` }, `·${d.depth}`), ' ', link(d.id), ' ', h('span', { class: 'ilist__sub' }, 'via ', link(d.via, d.via))]));
      out.push(section('dependencies', 'Dependencies', [
        deps.length ? h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, 'Depends on (transitive)'), depList(deps)) : null,
        dependents.length ? h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, 'Depended on by (transitive)'), depList(dependents)) : null,
      ]));
    }
    const contracts = contractsOf(model, c.id);
    if (contracts.length) out.push(section('contracts', 'Contracts', [ul(contracts.map((k) => [link(k.contract.id), ' ', h('span', { class: 'ilist__sub' }, `${k.role} via `, link(k.via, k.via))]))]));
    const kids = c.data.kind === 'subsystem' ? childrenOf(model, c.id) : [];
    if (kids.length) out.push(section('contains', 'Contains', [ul(kids.map((k) => entityRef(k.id)))]));
    const behaviors = (model.byKind.behavior ?? []).filter((/** @type {any} */ b) => b.data.subject === c.id);
    if (behaviors.length) out.push(section('behaviors', 'Behaviors', [ul(behaviors.map((b) => entityRef(b.id)))]));
    const claims = (model.byKind.claim ?? []).filter((/** @type {any} */ k) => (session.claimResult(k.id)?.involved ?? []).includes(c.id) || (k.data.subjects ?? []).includes(c.id));
    if (claims.length) {
      out.push(section('claims', 'Claims', [ul(claims.map((k) => {
        const r = session.claimResult(k.id);
        return [statusChip(r ? r.status : 'not-evaluated'), ' ', link(k.id)];
      }))]));
    }
    if (Array.isArray(c.data.unknowns) && c.data.unknowns.length) {
      out.push(section('unknowns', 'Known unknowns', [h('ul', { class: 'ilist ilist--unknowns' }, c.data.unknowns.map((/** @type {string} */ u) => h('li', { class: 'ilist__item ilist__item--unknown' }, u)))], 'emphasis'));
    }
    return out;
  }

  /** @param {any} r */
  function relationshipSection(r) {
    const model = session.model;
    const kind = model.meta.relationshipKinds[r.data.kind];
    /** @param {string} id */
    const end = (id) => {
      const e = model.entities.get(id);
      const comp = e && e.kind === 'port' ? componentOf(model, id) : null;
      return [link(id), e ? h('span', { class: 'ilist__sub' }, ` ${kindLabel(e.kind)}`) : null, comp ? [' of ', link(comp.id)] : null];
    };
    return section('semantics', 'Semantics', [kv([
      ['Kind', kind ? kind.label : r.data.kind],
      ['Meaning', kind?.description ?? 'This relationship kind is not defined in the meta-model.'],
      ['Dependency', kind ? (kind.dependency ? 'Counts as a dependency of the source on the target.' : 'Does not count as a dependency.') : '—'],
      ['From', ...end(r.data.from)],
      ['To', ...end(r.data.to)],
    ])]);
  }

  /** @param {any} claim */
  function claimSection(claim) {
    const model = session.model;
    const res = session.claimResult(claim.id);
    if (!res) return section('result', 'Evaluation result', [h('p', { class: 'insp__muted', 'data-testid': 'claim-result' }, 'Not evaluated.')]);
    const st = /** @type {Record<string, {label: string, tone: string}>} */ (CLAIM_STATUSES)[res.status];
    const parts = [kv([
      ['Status', statusChip(res.status, true)],
      ['Evaluator', h('code', { class: 'mono' }, res.evaluator)],
      ['Method', h('code', { class: 'mono' }, res.method ?? '—')],
      ['Model hash', h('code', { class: 'mono', title: res.semanticHash }, String(res.semanticHash).slice(0, 8))],
    ])];
    parts.push(h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, 'Scope'), h('p', { class: 'insp__text' }, res.scope)));
    parts.push(h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, 'Explanation'), h('p', { class: 'insp__text' }, res.explanation)));
    const cx = res.counterexample;
    if (cx) {
      const body = [h('p', { class: 'insp__text' }, cx.summary)];
      if (cx.entities?.length) body.push(h('div', { class: 'chips' }, cx.entities.map((/** @type {string} */ id) => link(id))));
      if (cx.path?.length) {
        const p = h('p', { class: 'insp__path' }, 'Path: ');
        cx.path.forEach((/** @type {string} */ id, /** @type {number} */ i) => { if (i) p.append(h('span', { class: 'crumbs__sep', 'aria-hidden': 'true' }, ' → ')); p.append(link(id)); });
        body.push(p);
      }
      if (cx.scenario) {
        const btn = h('button', { type: 'button', class: 'btn btn--small', 'data-testid': 'open-in-simulator' }, 'Open in simulator');
        on(btn, 'click', () => { session.simLoad(cx.scenario); if (typeof cx.stepIndex === 'number') session.simSeek(cx.stepIndex); });
        body.push(h('p', { class: 'insp__text' }, 'Scenario ', link(cx.scenario), typeof cx.stepIndex === 'number' ? ` at step ${cx.stepIndex}` : '', ' ', btn));
      }
      parts.push(h('div', { class: 'isub isub--counterexample' }, h('h4', { class: 'isub__head' }, 'Counterexample'), ...body));
    }
    if (res.assumptions?.length) {
      parts.push(h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, 'Assumptions'), h('p', { class: 'insp__muted' }, 'Holds only if:'),
        ul(res.assumptions.map((/** @type {string} */ id) => [link(id, id), ' ', h('span', { class: 'insp__text' }, model.entities.get(id)?.data.statement ?? '')]))));
    }
    if (res.evidence?.length) {
      parts.push(h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, 'Evidence'), ul(res.evidence.map((/** @type {any} */ ev) => [
        link(ev.id, ev.id), ' ', h('span', { class: 'mono' }, ev.kind), ' ', h('span', { class: 'mono ilist__sub' }, ev.ref), ' ',
        chip(ev.supports ? 'supports' : 'contradicts', 'none'), ' ',
        h('span', { class: 'ilist__sub' }, ev.recorded === 'pass' ? 'recorded pass' : ev.recorded === 'fail' ? 'recorded fail' : 'no recorded execution — author-entered'),
        ev.detail ? h('div', { class: 'insp__muted' }, ev.detail) : null,
      ]))));
    }
    return section('result', 'Evaluation result', [h('div', { 'data-testid': 'claim-result', 'data-status': res.status, 'data-tone': st?.tone ?? 'none' }, ...parts)]);
  }

  /** @param {any} b */
  function behaviorSections(b) {
    const model = session.model;
    const states = [...model.entities.values()].filter((e) => e.owner === b.id && e.kind === 'state');
    const trans = [...model.entities.values()].filter((e) => e.owner === b.id && e.kind === 'transition');
    const out = [];
    if (states.length) {
      out.push(section('states', 'States', [h('table', { class: 'itable cardtable' }, h('thead', {}, h('tr', {}, h('th', {}, 'State'), h('th', {}, 'Note'))),
        h('tbody', {}, states.map((s) => h('tr', {}, h('td', { class: 'cardtable__title' }, ...entityRef(s.id)), h('td', { 'data-label': 'Note' }, [b.data.initial === s.id ? 'initial' : null, s.data.terminal ? 'terminal' : null].filter(Boolean).join(', '))))))]));
    }
    if (trans.length) {
      out.push(section('transitions', 'Transitions', [h('table', { class: 'itable cardtable' }, h('thead', {}, h('tr', {}, h('th', {}, 'Transition'), h('th', {}, 'From'), h('th', {}, 'To'), h('th', {}, 'On'), h('th', {}, 'Guard'))),
        h('tbody', {}, trans.map((t) => h('tr', {}, h('td', { class: 'cardtable__title' }, link(t.id, t.id)), h('td', { 'data-label': 'From' }, link(t.data.from)), h('td', { 'data-label': 'To' }, link(t.data.to)), h('td', { 'data-label': 'On' }, link(t.data.on)),
          h('td', { class: 'mono', 'data-label': 'Guard' }, t.data.guard ?? '')))))]));
    }
    return out;
  }

  /** @param {any} s */
  function scenarioSections(s) {
    const model = session.model;
    const out = [];
    const load = h('button', { type: 'button', class: 'btn btn--small', 'data-testid': 'load-in-simulator' }, 'Load in simulator');
    on(load, 'click', () => session.simLoad(s.id));
    const steps = s.data.steps ?? [];
    out.push(section('steps', 'Scenario', [
      h('p', { class: 'insp__actions-inline' }, load),
      steps.length ? h('table', { class: 'itable cardtable' }, h('thead', {}, h('tr', {}, h('th', {}, 'At'), h('th', {}, 'Event'), h('th', {}, 'Payload'))),
        h('tbody', {}, steps.map((/** @type {any} */ st) => h('tr', {}, h('td', { class: 'mono', 'data-label': 'At' }, String(st.at)), h('td', { 'data-label': 'Event' }, link(st.event)), h('td', { class: 'mono', 'data-label': 'Payload' }, st.payload ? JSON.stringify(st.payload) : ''))))) : h('p', { class: 'insp__muted' }, 'No input events.'),
    ]));
    const faults = s.data.faults ?? [];
    if (faults.length) out.push(section('faults', 'Active faults', [ul(faults.map((/** @type {string} */ f) => [link(f), ' ', h('span', { class: 'ilist__sub mono' }, model.entities.get(f)?.data.kind ?? '')]))]));
    return out;
  }

  /** The reference column of a field: the principal, a record link, or nothing. @param {any} f */
  const fieldRef = (f) => (f.refersTo === PRINCIPAL ? h('span', { class: 'mono' }, 'principal id') : typeof f.refersTo === 'string' ? link(f.refersTo) : '');

  /** One line saying how fresh a copy is and when erasure reaches it. @param {any} c */
  function copyTerms(c) {
    const fr = c.data.freshness;
    const er = c.data.erasure;
    const fresh = fr && fr.bound !== undefined ? `fresh within ${fr.bound}${fr.unit ? ` ${fr.unit}${typeof fr.bound === 'number' && fr.bound !== 1 ? 's' : ''}` : ''}` : 'no freshness bound';
    const erase = er && typeof er.point === 'string' && er.point ? `erased: ${er.point}` : 'no erasure point';
    return `${fresh}; ${erase}`;
  }

  /** @param {any} r */
  function recordSections(r) {
    const model = session.model;
    const out = [];
    const fields = recordFields(r);
    const key = new Set(Array.isArray(r.data.key) ? r.data.key : []);
    out.push(section('fields', 'Fields', [fields.length ? h('table', { class: 'itable cardtable', 'data-testid': 'record-fields' },
      h('thead', {}, h('tr', {}, h('th', {}, 'Field'), h('th', {}, 'Type'), h('th', {}, 'Personal'), h('th', {}, 'Refers to'), h('th', {}, 'Role'))),
      h('tbody', {}, fields.map(({ field }) => h('tr', { 'data-field': field.name },
        h('td', { class: 'cardtable__title mono' }, field.name, key.has(field.name) ? h('span', { class: 'ilist__sub' }, ' key') : null),
        h('td', { class: 'mono', 'data-label': 'Type' }, String(field.type ?? '')),
        h('td', { 'data-label': 'Personal' }, typeof field.personal === 'string' ? chip(field.personal, 'warn') : ''),
        h('td', { 'data-label': 'Refers to' }, fieldRef(field)),
        h('td', { 'data-label': 'Role' }, typeof field.role === 'string' ? field.role : ''))))) : h('p', { class: 'insp__muted' }, 'No fields.')]));
    const copies = copiesOf(model, r.id);
    out.push(section('copies', 'Copies', [copies.length ? ul(copies.map((c) => [
      link(c.id), ' ', chip(String(c.data.scope), c.data.scope === 'shared' ? 'warn' : 'none'), ' ',
      h('span', { class: 'ilist__sub' }, 'held by '), typeof c.data.heldBy === 'string' ? link(c.data.heldBy) : '(none)',
      h('div', { class: 'insp__muted' }, copyTerms(c)),
    ])) : h('p', { class: 'insp__muted', 'data-testid': 'record-no-copies' }, 'No copy of this record is declared.')]));
    return out;
  }

  /** @param {any} c */
  function copySections(c) {
    const model = session.model;
    const sources = sourcesOf(model, c);
    const { held } = copyFields(model, c);
    return [section('copy-source', 'Source', [
      kv([
        ['Copy of', ...sources.flatMap((r, i) => [i ? ', ' : '', link(r.id)])],
        ['Held by', typeof c.data.heldBy === 'string' ? link(c.data.heldBy) : '(none)'],
        ['Scope', chip(String(c.data.scope), c.data.scope === 'shared' ? 'warn' : 'none')],
        ['Terms', copyTerms(c)],
      ]),
      h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, Array.isArray(c.data.fields) ? 'Fields held' : 'Fields held (every field of the source)'),
        held.length ? ul(held.map((hf) => [
          link(hf.record.id, hf.record.id), h('span', { class: 'mono' }, `.${hf.field.name}`), ' ', h('span', { class: 'ilist__sub mono' }, String(hf.field.type ?? '')),
          isPrincipalData(hf.field) ? [' ', chip(typeof hf.field.personal === 'string' ? `personal: ${hf.field.personal}` : 'principal id', 'warn')] : null,
        ])) : h('p', { class: 'insp__muted' }, 'No field resolved.')),
    ])];
  }

  /** @param {any} entity */
  function referencedBy(entity) {
    const model = session.model;
    const refs = inboundRefs(model, entity.id);
    if (!refs.length) return null;
    /** @type {Map<string, Set<string>>} */
    const by = new Map();
    for (const r of refs) {
      const from = model.entities.get(r.from);
      const via = from ? r.path.slice(from.path.length).filter((/** @type {any} */ s) => typeof s === 'string').join('.') : '';
      if (!by.has(r.from)) by.set(r.from, new Set());
      by.get(r.from)?.add(via);
    }
    return section('referenced-by', 'Referenced by', [ul([...by].map(([id, vias]) => [h('span', { class: 'ilist__sub' }, `${kindLabel(model.entities.get(id)?.kind ?? '')} `), link(id), ' ', h('span', { class: 'ilist__sub mono' }, [...vias].filter(Boolean).join(', '))]))]);
  }

  /** @param {any} entity */
  function actions(entity) {
    const buttons = [];
    if (entity.kind === 'component') {
      const connect = h('button', { type: 'button', class: 'btn', 'data-testid': 'inspector-connect' }, 'Connect to…');
      on(connect, 'click', () => openConnectDialog(session, entity.id, null, { opener: connect }));
      buttons.push(connect);
      if (entity.data.kind === 'subsystem') {
        const add = h('button', { type: 'button', class: 'btn', 'data-testid': 'inspector-new-inside' }, 'New component inside');
        on(add, 'click', () => openCreateDialog(session, { parent: entity.id, opener: add }));
        buttons.push(add);
      }
    }
    if (entity.kind !== 'system') {
      const del = h('button', { type: 'button', class: 'btn btn--danger', 'data-testid': 'inspector-delete' }, 'Delete…');
      on(del, 'click', () => openDeleteDialog(session, entity.id, { opener: del }));
      buttons.push(del);
    }
    return buttons.length ? section('actions', 'Actions', [h('div', { class: 'insp__actions' }, buttons)]) : null;
  }

  /** @param {any} model */
  function overview(model) {
    const diags = session.diagnostics ?? [];
    const errors = diags.filter((/** @type {any} */ d) => d.severity === 'error').length;
    const warnings = diags.filter((/** @type {any} */ d) => d.severity === 'warning').length;
    const gaps = diags.filter((/** @type {any} */ d) => d.severity === 'info').length;
    const counts = Object.keys(model.meta.entities).filter((k) => k !== 'system').map((k) => [kindLabel(k), String(model.byKind[k]?.length ?? 0)]);
    return section('summary', 'Model summary', [
      kv(counts.map(([k, v]) => [k, h('span', { class: 'mono' }, v)])),
      kv([
        ['Errors', h('span', { class: 'mono', 'data-testid': 'summary-errors' }, String(errors))],
        ['Warnings', h('span', { class: 'mono', 'data-testid': 'summary-warnings' }, String(warnings))],
        ['Gaps', h('span', { class: 'mono', 'data-testid': 'summary-gaps' }, String(gaps))],
        ['Semantic hash', h('code', { class: 'mono', title: session.project?.semanticHash ?? '' }, String(session.project?.semanticHash ?? '').slice(0, 12))],
      ]),
    ]);
  }

  // ---- render ------------------------------------------------------------

  function captureFocus() {
    const a = /** @type {any} */ (document.activeElement);
    if (!a || !root.contains(a)) return null;
    const w = /** @type {HTMLElement|null} */ (a.closest('[data-prop]'));
    if (!w) return null;
    const focusables = [...w.querySelectorAll('input,select,textarea,button')];
    return { prop: w.dataset.prop, index: Math.max(0, focusables.indexOf(a)), start: a.selectionStart ?? null, end: a.selectionEnd ?? null };
  }

  /** @param {ReturnType<typeof captureFocus>} f */
  function restoreFocus(f) {
    if (!f) return;
    const w = [...root.querySelectorAll('[data-prop]')].find((n) => /** @type {HTMLElement} */ (n).dataset.prop === f.prop);
    const target = /** @type {any} */ (w ? [...w.querySelectorAll('input,select,textarea,button')][f.index] : null);
    if (!target) return;
    target.focus({ preventScroll: true });
    try { if (f.start !== null && target.setSelectionRange && target.type !== 'number' && target.type !== 'checkbox') target.setSelectionRange(f.start, f.end); } catch { /* not a text control */ }
  }

  function render() {
    pending = 0;
    const model = session.model;
    const id = session.selection;
    const entity = model && id ? model.entities.get(id) : null;
    const same = (entity?.id ?? model?.system?.id ?? null) === lastId;
    const focus = same ? captureFocus() : null;
    const top = el.scrollTop;
    clear(root);
    if (!model) {
      root.append(h('p', { class: 'insp__muted' }, 'No specification is loaded.'));
      lastId = null;
      return;
    }
    const shown = entity ?? model.system;
    root.dataset.entityId = shown.id;
    if (!entity) root.append(overview(model));
    root.append(identity(shown), properties(shown));
    root.append(...[diagnosticsSection(shown)].filter(Boolean));
    if (shown.kind === 'component') root.append(...componentSections(shown));
    else if (shown.kind === 'relationship') root.append(relationshipSection(shown));
    else if (shown.kind === 'claim') root.append(claimSection(shown));
    else if (shown.kind === 'behavior') root.append(...behaviorSections(shown));
    else if (shown.kind === 'scenario') root.append(...scenarioSections(shown));
    else if (shown.kind === 'record') root.append(...recordSections(shown));
    else if (shown.kind === 'copy') root.append(...copySections(shown));
    const refd = referencedBy(shown);
    if (refd) root.append(refd);
    const act = actions(shown);
    if (act) root.append(act);
    lastId = shown.id;
    el.scrollTop = same ? top : 0;
    restoreFocus(focus);
  }

  /** Renders after the current event (and any focus move) has settled. */
  function schedule() {
    if (pending) return;
    pending = /** @type {any} */ (setTimeout(render, 0));
  }
  function now() {
    if (pending) { clearTimeout(pending); pending = 0; }
    render();
  }

  const unsubs = [
    session.on('selection', now),
    session.on('project', now),
    session.on('model', schedule),
    session.on('claims', schedule),
  ];
  render();
  return () => { if (pending) clearTimeout(pending); for (const u of unsubs) u(); clear(el); };
}
