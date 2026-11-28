// The semantic inspector. The property editor is generated from the effective
// meta-model (property-controls.js); the other sections are read-only queries
// over the model and the claim results, each entry a link to the entity it names.

import { h, clear, on } from './dom.js';
import { entityLabel, relationshipsOf, dependencies, contractsOf, childrenOf, ancestorsOf, inboundRefs, componentOf, elementsOf } from '../core/query.js';
import { baseFacts, blockReport, deriveModel, witnessOf } from '../core/abstraction.js';
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
    if (res.modelledBy?.length) {
      parts.push(h('div', { class: 'isub', 'data-testid': 'claim-modelled-by' }, h('h4', { class: 'isub__head' }, 'Checked over the behavior model by'),
        ul(res.modelledBy.map((/** @type {{claimId: string, status: string}} */ m) => [link(m.claimId, m.claimId), ' ', statusChip(m.status, true)]))));
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

  // ---- multiscale (WG-5695): what a drawn fact stands for, and what a block is at the current cut -------------

  /** The label of an element: its entity's, or a module element's path. @param {string} id */
  const elementName = (id) => { const e = session.model.entities.get(id); return e ? entityLabel(e) : id.startsWith('module:') ? id.slice(7) : id; };

  /** A button that selects an element (an entity, or a module element). @param {string} id */
  function elementLink(id) {
    if (session.model.entities.has(id)) return link(id);
    const b = h('button', { type: 'button', class: 'ilink mono', 'data-entity-id': id, title: `Module element ${id}` }, elementName(id));
    on(b, 'click', () => session.select(id));
    return b;
  }

  /**
   * The derived interaction (or path summary) a selected relationship is a witness of in the current structural
   * scene: every witness with its kind, contract, carried data and provenance, each one a link to the relationship.
   * @param {any} r
   */
  function interactionSection(r) {
    const model = session.model;
    const scene = session.scene;
    if (scene?.projection !== 'structural') return null;
    const on1 = session.selectedEdge ? scene.edges.find((/** @type {any} */ e) => e.id === session.selectedEdge && (e.witnesses ?? []).includes(r.id)) : null;
    const edge = on1 ?? scene.edges.find((/** @type {any} */ e) => !e.pathSummary && (e.witnesses ?? []).includes(r.id));
    if (!edge) {
      const d = scene.abstraction ? deriveModel(model, { hierarchy: scene.abstraction.hierarchy, blocks: scene.abstraction.blocks }) : null;
      const w = d ? witnessOf(d, r.id) : null;
      const text = w?.fibre ? `At this cut it lies inside the block ${elementName(w.fibre)}, so it is not drawn; expanding that block shows it.`
        : w?.interaction ? `At this cut it is a witness of ${elementName(w.interaction.from)} → ${elementName(w.interaction.to)} (${w.interaction.kind}), which this view's filter does not draw.`
          : 'It is not placed at this cut.';
      return section('interaction', 'At this cut', [h('p', { class: 'insp__text', 'data-testid': 'interaction-not-drawn' }, text)]);
    }
    const facts = baseFacts(model).byId;
    const kind = (/** @type {string} */ k) => model.meta.relationshipKinds[k]?.label ?? k;
    const rows = (edge.witnesses ?? []).map((/** @type {string} */ w) => {
      const f = facts.get(w);
      const rel = model.entities.get(w);
      const btn = h('button', { type: 'button', class: 'ilink', 'data-entity-id': w, title: `Relationship ${w}` }, w);
      on(btn, 'click', () => session.select(w, { edge: edge.id }));
      return h('li', { class: 'ilist__item witness', 'data-testid': 'witness-row', 'data-witness': w, 'aria-current': String(w === r.id) },
        h('div', { class: 'witness__head' }, chip(kind(f?.kind ?? rel?.data.kind), 'none'), ' ', btn),
        f ? h('div', { class: 'witness__ends ilist__sub' }, elementName(f.from), f.fromPort ? ` (port ${f.fromPort})` : '', ' → ', elementName(f.to), f.toPort ? ` (port ${f.toPort})` : '') : null,
        h('dl', { class: 'kv witness__kv' },
          h('div', { class: 'kv__row' }, h('dt', { class: 'kv__k' }, 'Contract'), h('dd', { class: 'kv__v', 'data-field': 'contract' }, f?.contract ? link(f.contract) : '—')),
          h('div', { class: 'kv__row' }, h('dt', { class: 'kv__k' }, 'Carries'), h('dd', { class: 'kv__v', 'data-field': 'carries' }, f?.carries.length ? f.carries.flatMap((c, i) => [i ? ', ' : '', link(c)]) : '—')),
          h('div', { class: 'kv__row' }, h('dt', { class: 'kv__k' }, 'Provenance'), h('dd', { class: 'kv__v', 'data-field': 'provenance' }, f?.provenance ?? 'declared'))));
    });
    const head = edge.pathSummary
      ? `Derived path summary: ${elementName(edge.from)} may reach ${elementName(edge.to)} through ${edge.pathSummary.via.map(elementName).join(', ')}, which ${edge.pathSummary.via.length === 1 ? 'is' : 'are'} hidden. It is a may-path: a path through a block need not be a path through its members. These are the relationships along it.`
      : `${elementName(edge.from)} → ${elementName(edge.to)}: ${kind(edge.kind)}, one derived interaction at this cut standing for ${rows.length} ${rows.length === 1 ? 'relationship' : 'relationships'}.`;
    const marks = (edge.marks ?? []).map((/** @type {any} */ m) => h('li', { class: 'ilist__item', 'data-mark': m.kind }, chip(m.text, 'warn'), ' ', m.title ?? ''));
    return section('interaction', edge.pathSummary ? 'Path summary' : 'Derived interaction', [
      h('div', { 'data-testid': 'derived-interaction', 'data-edge': edge.id, 'data-key': edge.key ?? '', 'data-count': String(rows.length) },
        h('p', { class: 'insp__text' }, head),
        marks.length ? h('ul', { class: 'ilist' }, marks) : null,
        h('h4', { class: 'isub__head' }, `Witnesses (${rows.length})`),
        h('ul', { class: 'ilist witness-list', 'data-testid': 'witness-list' }, rows)),
    ]);
  }

  const KNOWLEDGE_TEXT = { transparent: 'Transparent', opaque: 'Opaque', unknown: 'Unknown' };
  const AGREEMENT_TEXT = {
    agrees: 'Agrees: every declared port is realised on the boundary and every typed boundary group is covered by a port.',
    disagrees: 'Disagrees (V3): see the findings below.',
    'no-declared-interface': 'No declared interface: the block declares no ports, so its derived interface is all there is.',
  };

  /**
   * An element as a block of the current structural cut: purpose, responsibilities, knowledge status, boundary,
   * derived interface, declared interface with the agreement result, and the findings about it.
   * @param {string} id
   */
  function blockSections(id) {
    const model = session.model;
    const nav = session.currentCut?.();
    if (!nav) return [];
    const rep = blockReport(model, nav.hierarchy, nav.expanded, id);
    if (!rep) return [];
    const out = [];
    const opened = nav.opened.includes(id);
    const isBlock = nav.blocks.includes(id);
    const actions = [];
    if (isBlock && rep.members) {
      const b = h('button', { type: 'button', class: 'btn btn--small', 'data-testid': 'block-expand' }, `Expand into its ${rep.members} ${rep.members === 1 ? 'member' : 'members'}`);
      on(b, 'click', () => session.toggleCollapsed(id));
      actions.push(b);
    }
    if (opened) {
      const b = h('button', { type: 'button', class: 'btn btn--small', 'data-testid': 'block-collapse' }, 'Collapse into one block');
      on(b, 'click', () => session.toggleCollapsed(id));
      actions.push(b);
    }
    const where = isBlock ? 'A block of the current cut.' : opened ? 'Opened at the current cut; described here as the block it is when collapsed.' : 'Inside a block of the current cut; described here as the block it is when revealed.';
    const k = rep.knowledge;
    out.push(section('block', 'Block at this cut', [h('div', { 'data-testid': 'block-panel', 'data-element': id },
      h('p', { class: 'insp__text' }, where),
      kv([
        ['Purpose', h('span', { 'data-testid': 'block-purpose', 'data-stated': String(rep.purpose !== null) }, rep.purpose ?? (rep.kind === 'module' ? 'A module element: its purpose is that of the component declaring it.' : 'No purpose is stated (the first coherence condition of a level is not met).'))],
        ['Knowledge', h('span', { 'data-testid': 'block-knowledge', 'data-status': k?.status ?? '', 'data-planned': String(rep.planned) },
          chip(`${/** @type {any} */ (KNOWLEDGE_TEXT)[k?.status ?? ''] ?? '—'}${rep.planned ? ', planned' : ''}`, k?.status === 'transparent' ? 'ok' : k?.status === 'unknown' ? 'warn' : 'none'), ' ', k?.reason ?? '')],
        rep.kind === 'module' ? ['Declared by', ...rep.owners.flatMap((o, i) => [i ? ', ' : '', link(o)])] : null,
        ['Members', h('span', { class: 'mono' }, String(rep.members))],
      ]),
      rep.responsibilities.length ? h('div', { class: 'isub' }, h('h4', { class: 'isub__head' }, 'Responsibilities'), h('ul', { class: 'ilist', 'data-testid': 'block-responsibilities' }, rep.responsibilities.map((t) => h('li', { class: 'ilist__item' }, t)))) : null,
      actions.length ? h('p', { class: 'insp__actions-inline' }, ...actions) : null)]));

    const relList = (/** @type {string[]} */ ids) => h('ul', { class: 'ilist' }, ids.map((w) => h('li', { class: 'ilist__item' }, link(w, w))));
    out.push(section('boundary', 'Boundary', [h('div', { 'data-testid': 'block-boundary', 'data-out': String(rep.boundary.out.length), 'data-in': String(rep.boundary.in.length) },
      h('p', { class: 'insp__text' }, `${rep.boundary.out.length} ${rep.boundary.out.length === 1 ? 'relationship leaves' : 'relationships leave'} it and ${rep.boundary.in.length} ${rep.boundary.in.length === 1 ? 'enters' : 'enter'} it: the relationships with exactly one end inside.`),
      rep.boundary.out.length ? h('details', { class: 'isub' }, h('summary', { class: 'isub__head' }, `Outgoing (${rep.boundary.out.length})`), relList(rep.boundary.out)) : null,
      rep.boundary.in.length ? h('details', { class: 'isub' }, h('summary', { class: 'isub__head' }, `Incoming (${rep.boundary.in.length})`), relList(rep.boundary.in)) : null)]));

    const groups = rep.interface.groups;
    out.push(section('derived-interface', 'Derived interface', [groups.length ? h('table', { class: 'itable cardtable', 'data-testid': 'block-interface' },
      h('thead', {}, h('tr', {}, h('th', {}, 'Direction'), h('th', {}, 'Kind'), h('th', {}, 'Contract'), h('th', {}, 'Relationships'), h('th', {}, 'Events'), h('th', {}, 'Declared by'))),
      h('tbody', {}, groups.map((g) => h('tr', { 'data-testid': 'interface-group', 'data-group': g.id },
        h('td', { class: 'cardtable__title' }, g.direction === 'out' ? 'Requires (out)' : 'Provides (in)'),
        h('td', { 'data-label': 'Kind' }, model.meta.relationshipKinds[g.kind]?.label ?? g.kind),
        h('td', { 'data-label': 'Contract' }, g.contract ? link(g.contract) : '—'),
        h('td', { 'data-label': 'Relationships', class: 'mono' }, String(g.witnesses.length)),
        h('td', { 'data-label': 'Events' }, g.events.length ? g.events.flatMap((e, i) => [i ? ', ' : '', link(e)]) : '—'),
        h('td', { 'data-label': 'Declared by' }, g.matchedBy.length ? g.matchedBy.flatMap((p, i) => [i ? ', ' : '', link(p)]) : '—')))))
      : h('p', { class: 'insp__muted', 'data-testid': 'block-interface-empty' }, 'Nothing crosses its boundary, so its derived interface is empty.')]));

    const ports = rep.interface.ports;
    out.push(section('declared-interface', 'Declared interface', [h('div', { 'data-testid': 'block-ports', 'data-ports': String(ports.length) },
      h('p', { class: 'insp__text', 'data-testid': 'block-agreement', 'data-agreement': rep.agreement }, /** @type {any} */ (AGREEMENT_TEXT)[rep.agreement]),
      rep.interface.authority === 'declared' ? h('p', { class: 'insp__muted' }, 'It is opaque: its declared interface is authoritative.') : null,
      ports.length ? h('ul', { class: 'ilist' }, ports.map((p) => h('li', { class: 'ilist__item', 'data-port': p.port }, link(p.port), ' ', h('span', { class: 'ilist__sub' }, `${p.direction}${p.contract ? ` ${p.contract}` : ''}`), ' ',
        p.matches.length ? chip(`realised by ${p.matches.length} ${p.matches.length === 1 ? 'group' : 'groups'}`, 'ok') : chip('realised by nothing', 'warn')))) : null)]));

    const findings = rep.diagnostics;
    out.push(section('coherence', 'Findings at this cut', [findings.length
      ? h('ul', { class: 'ilist', 'data-testid': 'block-findings' }, findings.map((x) => h('li', { class: 'ilist__item', 'data-code': x.code }, chip(x.condition, x.severity === 'error' ? 'bad' : 'warn'), ' ', x.message)))
      : h('p', { class: 'insp__muted', 'data-testid': 'block-findings' }, `No finding: the partition is well formed here and the interface conditions hold. ${rep.coherence.note}`)]));
    return out;
  }

  /** A claim stated at a cut, with its result at the cut the current view draws. @param {any} claim */
  function claimAtCutSection(claim) {
    const at = (session.scene?.levelClaims ?? []).find((/** @type {any} */ c) => c.claimId === claim.id);
    if (!at) return null;
    return section('claim-at-cut', 'At the current cut', [h('div', { 'data-testid': 'claim-at-cut', 'data-status': at.status, 'data-expressible': String(at.expressible) },
      at.expressible ? statusChip(at.status, true) : chip('Not expressible at this level', 'warn'),
      h('p', { class: 'insp__text' }, at.explanation),
      at.drawn.length || at.notDrawn.length ? h('p', { class: 'insp__muted' }, `Its counterexample: ${at.drawn.length} drawn in red at this cut${at.notDrawn.length ? `, ${at.notDrawn.length} not drawn here (${at.notDrawn.join(', ')})` : ''}.`) : null)]);
  }

  /** The inspector of a module element: what it is, and the block it is at the current cut. @param {string} id */
  function moduleSections(id) {
    const el = elementsOf(session.model).get(id);
    return [section('identity', 'Identity', [kv([
      ['Kind', 'Module element'],
      ['Label', h('strong', { class: 'insp__title' }, elementName(id))],
      ['Id', h('code', { class: 'mono' }, id)],
      ['Declared by', ...(el?.owners ?? []).flatMap((o, i) => [i ? ', ' : '', link(o)])],
    ])]), ...blockSections(id)];
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
    // A module element is an element no entity declares: it is shown as the block it is.
    if (!entity && id && elementsOf(model).has(id)) {
      root.dataset.entityId = id;
      root.append(...moduleSections(id));
      lastId = id;
      el.scrollTop = same ? top : 0;
      return;
    }
    const shown = entity ?? model.system;
    root.dataset.entityId = shown.id;
    if (!entity) root.append(overview(model));
    root.append(identity(shown), properties(shown));
    root.append(...[diagnosticsSection(shown)].filter(Boolean));
    if (shown.kind === 'component' || shown.kind === 'system') root.append(...blockSections(shown.id));
    if (shown.kind === 'component') root.append(...componentSections(shown));
    else if (shown.kind === 'relationship') root.append(...[interactionSection(shown), relationshipSection(shown)].filter(Boolean));
    else if (shown.kind === 'claim') root.append(...[claimAtCutSection(shown), claimSection(shown)].filter(Boolean));
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
    // The cut changed: the block panel and the derived interaction of the selection change with it.
    session.on('scene', schedule),
  ];
  render();
  return () => { if (pending) clearTimeout(pending); for (const u of unsubs) u(); clear(el); };
}
