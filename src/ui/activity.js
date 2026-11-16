// Bottom-panel activity views: diagnostics and the change log.

import { h, clear, icon } from './dom.js';
import { detailText } from './detail.js';

const SEVERITIES = /** @type {const} */ ([
  ['error', 'Errors', 'error'],
  ['warning', 'Warnings', 'warning'],
  ['info', 'Gaps', 'info'],
]);

/** @param {string} s */
const short = (s) => String(s ?? '').slice(0, 8);

/**
 * One diagnostic line. A button when it can point at an entity, else plain.
 * @param {any} session @param {any} d
 */
function diagnosticRow(session, d) {
  const loc = d.loc ? `${d.loc.line}:${d.loc.column}` : '';
  const content = [
    h('span', { class: ['diag__mark', `diag__mark--${d.severity}`], 'aria-hidden': 'true' }, icon(d.severity === 'info' ? 'info' : d.severity, 12)),
    h('span', { class: 'diag__code' }, d.code),
    h('span', { class: 'diag__message' }, d.message),
    h('span', { class: 'diag__loc' }, loc),
  ];
  const label = `${d.severity}: ${d.message}${loc ? ' at ' + loc : ''}`;
  if (d.entityId) {
    return h('li', { class: 'diag', 'data-severity': d.severity, 'data-entity-id': d.entityId },
      h('button', {
        type: 'button', class: 'diag__btn', title: `${d.entityId}: select and show in source`, 'aria-label': label,
        onclick: () => { session.select(d.entityId, { source: 'diagnostics' }); session.revealSource(d.entityId); },
      }, ...content));
  }
  return h('li', { class: 'diag', 'data-severity': d.severity },
    h('div', { class: 'diag__static', title: label }, ...content));
}

/**
 * @param {HTMLElement} el
 * @param {any} session
 * @returns {() => void} dispose
 */
export function mountDiagnostics(el, session) {
  const render = () => {
    const ds = /** @type {any[]} */ (session.diagnostics ?? []);
    clear(el);
    const root = h('div', { class: 'activity activity--diagnostics' });
    const count = (/** @type {string} */ s) => ds.filter((d) => d.severity === s).length;
    const e = count('error'), w = count('warning'), g = count('info');
    root.append(h('p', { class: 'activity__summary', 'data-testid': 'diagnostics-summary' },
      h('span', { class: e ? 'tone--bad' : 'muted' }, `${e} error${e === 1 ? '' : 's'}`), ' · ',
      h('span', { class: w ? 'tone--warn' : 'muted' }, `${w} warning${w === 1 ? '' : 's'}`), ' · ',
      h('span', { class: g ? 'diag__gap-count' : 'muted' }, `${g} gap${g === 1 ? '' : 's'}`)));
    if (!ds.length) {
      root.append(h('div', { class: 'activity__empty' },
        h('p', null, 'No diagnostics. The specification is well-formed.'),
        h('p', { class: 'muted' }, 'Well-formed is not the same as correct; see Verification.')));
    } else {
      for (const [sev, title] of SEVERITIES) {
        const list = ds.filter((d) => d.severity === sev);
        if (!list.length) continue;
        root.append(h('section', { class: 'diag-group', 'aria-label': title },
          h('h3', { class: 'diag-group__title' }, title, h('span', { class: 'diag-group__count' }, String(list.length))),
          h('ul', { class: 'diag-group__list' }, list.map((d) => diagnosticRow(session, d)))));
      }
    }
    el.append(root);
  };
  render();
  const offs = [session.on('model', render), session.on('project', render)];
  return () => { for (const off of offs) off(); };
}

/**
 * @param {HTMLElement} el
 * @param {any} session
 * @returns {() => void} dispose
 */
export function mountChanges(el, session) {
  /** @param {string} id */
  const chip = (id) => h('button', {
    type: 'button', class: 'chip', 'data-entity-id': id, title: `Select ${id}`,
    onclick: () => session.select(id, { source: 'changes' }),
  }, id);

  const historyItem = (/** @type {any} */ en) => {
    const affected = /** @type {string[]} */ (en.affected ?? []);
    const shown = affected.slice(0, 8);
    return h('li', { class: 'change', 'data-kind': 'history', 'data-revision': en.revision },
      h('div', { class: 'change__head' },
        h('span', { class: 'change__rev' }, `rev ${en.revision}`),
        h('span', { class: 'change__label', title: en.label }, en.label),
        h('span', { class: 'chip chip--origin', title: 'Where the change came from' }, en.origin),
        en.semanticChanged
          ? h('span', { class: 'badge badge--semantic', title: 'The semantic hash changed: the meaning of the specification changed' }, 'semantic')
          : h('span', { class: 'badge badge--presentation', title: 'The semantic hash is unchanged' }, 'presentation only')),
      en.semanticChanged
        ? h('div', { class: 'change__hash' }, h('code', null, short(en.hashBefore)), ' → ', h('code', null, short(en.hashAfter)))
        : null,
      affected.length
        ? h('div', { class: 'change__chips' }, shown.map(chip), affected.length > shown.length ? h('span', { class: 'muted' }, `+${affected.length - shown.length} more`) : null)
        : null);
  };

  const logItem = (/** @type {any} */ l) => h('li', { class: ['change', `change--${l.kind}`], 'data-kind': l.kind },
    h('div', { class: 'change__head' },
      h('span', { class: ['badge', `badge--${l.kind}`] }, l.kind),
      h('span', { class: 'change__label', title: l.message }, l.message)),
    detailText(l.detail) ? h('div', { class: 'change__detail' }, detailText(l.detail)) : null,
    Array.isArray(l.diagnostics) && l.diagnostics.length
      ? h('ul', { class: 'change__diags' }, l.diagnostics.map((/** @type {any} */ d) => h('li', { class: 'change__diag' },
        h('span', { class: 'diag__code' }, d.code), h('span', { class: 'diag__message' }, d.message),
        h('span', { class: 'diag__loc' }, d.loc ? `${d.loc.line}:${d.loc.column}` : ''))))
      : null);

  const render = () => {
    clear(el);
    const history = /** @type {any[]} */ (session.project?.history ?? []);
    const log = /** @type {any[]} */ (session.log ?? []);
    const changes = log.filter((l) => l.kind === 'change');
    const others = log.filter((l) => l.kind === 'error' || l.kind === 'info' || l.kind === 'save');
    // History entries carry no sequence number; align them with the 'change' log entries from the end.
    const offset = changes.length - history.length;
    /** @type {{key: number, node: HTMLElement}[]} */
    const items = [];
    history.forEach((en, j) => {
      const c = changes[offset + j];
      items.push({ key: c ? c.seq : -1 - (history.length - j), node: historyItem(en) });
    });
    for (const l of others) items.push({ key: l.seq, node: logItem(l) });
    items.sort((a, b) => b.key - a.key);

    const root = h('div', { class: 'activity activity--changes' });
    if (!items.length) {
      root.append(h('div', { class: 'activity__empty' }, h('p', null, 'No changes yet in this session.'),
        h('p', { class: 'muted' }, 'Every committed transaction, undo, redo and reload is listed here, newest first.')));
    } else {
      root.append(h('p', { class: 'activity__summary' }, `${history.length} commit${history.length === 1 ? '' : 's'} this session`),
        h('ol', { class: 'changes' }, items.map((i) => i.node)));
    }
    el.append(root);
  };
  render();
  const offs = [session.on('model', render), session.on('project', render), session.on('log', render)];
  return () => { for (const off of offs) off(); };
}
