// ARCHITECTURE.md: human-readable architecture documentation generated from the
// semantic model. Sections are omitted when they have nothing to show.

import { entityLabel, childrenOf, relationshipsOf, contractsOf } from '../query.js';
import { stableStringify, semanticHash } from '../hash.js';
import { text, oneLine, cell, list, nameOf, markdown, statusLabel } from './manifest.js';
import { claimRows } from './claims-report.js';

/** @typedef {import('../types.js').Model} Model */
/** @typedef {import('../types.js').Entity} Entity */
/** @typedef {import('../claims.js').ClaimResult} ClaimResult */

/**
 * @param {Model} model @param {any} c
 */
function categoryLabel(model, c) {
  const id = c.data.category;
  return model.meta.categories?.[id]?.label ? text(model.meta.categories[id].label) : text(id);
}

/**
 * A declared item (input, output, error, payload field, ...) as one line.
 * @param {any} v
 */
function itemLine(v) {
  if (v && typeof v === 'object' && !Array.isArray(v)) {
    const head = v.name !== undefined ? oneLine(v.name) : '';
    const type = v.type !== undefined ? ` (${oneLine(v.type)})` : '';
    const rest = v.description ?? v.condition;
    return [head + type, rest !== undefined ? oneLine(rest) : ''].filter(Boolean).join(': ');
  }
  return oneLine(v);
}

/**
 * One relationship as a bullet: kind label, the other end, and the description.
 * @param {Model} model
 * @param {{relationship: Entity, direction: 'out'|'in', other: Entity|undefined, viaPort?: string}} r
 */
function relationshipLine(model, r) {
  const d = r.relationship.data;
  const kindLabel = model.meta.relationshipKinds?.[d.kind]?.label ? text(model.meta.relationshipKinds[d.kind].label) : text(d.kind);
  const otherId = r.direction === 'out' ? d.to : d.from;
  const other = r.other ? oneLine(entityLabel(r.other)) : text(otherId);
  const via = r.viaPort ? ` (via port \`${oneLine(r.viaPort)}\`)` : '';
  const desc = d.description ? `: ${oneLine(d.description)}` : '';
  return `- ${kindLabel} → ${other}${via}${desc}`;
}

/**
 * @param {Model} model @param {Entity} c @param {string[]} L
 */
function componentSection(model, c, L) {
  const d = c.data;
  L.push(`### ${oneLine(entityLabel(c))}`, '');
  if (d.purpose) L.push(text(d.purpose), '');

  const meta = [`- Category: ${categoryLabel(model, c)}`];
  if (d.parent) meta.push(`- Parent: ${nameOf(model, d.parent)} (\`${oneLine(d.parent)}\`)`);
  if (d.owner) meta.push(`- Owner: ${oneLine(d.owner)}`);
  if (d.trustZone) meta.push(`- Trust zone: ${oneLine(d.trustZone)}`);
  L.push(...meta, '');

  const responsibilities = list(d.responsibilities);
  if (responsibilities.length) L.push('#### Responsibilities', '', ...responsibilities.map((r) => `- ${oneLine(r)}`), '');

  const ports = (model.byKind.port ?? []).filter((p) => p.owner === c.id);
  if (ports.length) {
    L.push(
      '#### Ports', '',
      '| Name | Id | Direction | Contract | Protocol |', '| --- | --- | --- | --- | --- |',
      ...ports.map((p) => `| ${cell(p.data.name ?? entityLabel(p))} | ${cell(p.id)} | ${cell(p.data.direction)} | ${cell(p.data.contract ? nameOf(model, p.data.contract) : '')} | ${cell(p.data.protocol)} |`),
      '',
    );
  }

  const rels = relationshipsOf(model, c.id);
  const out = rels.filter((r) => r.direction === 'out');
  const inbound = rels.filter((r) => r.direction === 'in');
  if (out.length) L.push('#### Relationships out', '', ...out.map((r) => relationshipLine(model, r)), '');
  if (inbound.length) L.push('#### Relationships in', '', ...inbound.map((r) => relationshipLine(model, r)), '');

  const contracts = contractsOf(model, c.id);
  if (contracts.length) {
    L.push('#### Contracts bound', '', ...contracts.map((k) => `- ${oneLine(entityLabel(k.contract))} (\`${oneLine(k.contract.id)}\`): ${k.role}, via \`${oneLine(k.via)}\``), '');
  }

  const unknowns = list(d.unknowns);
  if (unknowns.length) L.push('#### Known unknowns', '', ...unknowns.map((u) => `- ${oneLine(u)}`), '');

  if (d.implementation && typeof d.implementation === 'object') {
    const impl = d.implementation;
    const b = [`- Status: ${oneLine(impl.status)}`];
    const modules = list(impl.modules);
    if (modules.length) b.push(`- Modules: ${modules.map((m) => `\`${oneLine(m)}\``).join(', ')}`);
    if (impl.notes) b.push(`- Notes: ${oneLine(impl.notes)}`);
    L.push('#### Implementation', '', ...b, '');
  }

  if (d.illustrative === true) L.push('Illustrative.', '');
}

/**
 * @param {Model} model @param {Entity} b @param {string[]} L
 */
function behaviorSection(model, b, L) {
  const d = b.data;
  L.push(`### ${oneLine(entityLabel(b))}`, '');
  if (d.description) L.push(text(d.description), '');
  L.push(`- Subject: ${nameOf(model, d.subject)}`, `- Initial state: ${nameOf(model, d.initial)}`, '');

  const variables = list(d.variables);
  if (variables.length) {
    L.push(
      '#### Variables', '',
      '| Name | Type | Initial |', '| --- | --- | --- |',
      ...variables.map((v) => `| ${cell(v.name)} | ${cell(v.type)} | ${cell(renderValue(v.initial))} |`),
      '',
    );
  }

  const states = (model.byKind.state ?? []).filter((s) => s.owner === b.id);
  if (states.length) {
    L.push(
      '#### States', '',
      '| Id | Name | Terminal |', '| --- | --- | --- |',
      ...states.map((s) => `| ${cell(s.id)} | ${cell(entityLabel(s))} | ${s.data.terminal === true ? 'yes' : 'no'} |`),
      '',
    );
  }

  const transitions = (model.byKind.transition ?? []).filter((t) => t.owner === b.id);
  if (transitions.length) {
    L.push(
      '#### Transitions', '',
      '| Id | From | To | On | Guard | Effects | Fault only |', '| --- | --- | --- | --- | --- | --- | --- |',
      ...transitions.map((t) => `| ${cell(t.id)} | ${cell(nameOf(model, t.data.from))} | ${cell(nameOf(model, t.data.to))} | ${cell(nameOf(model, t.data.on))} | ${cell(t.data.guard)} | ${cell(effectsText(t.data.effects))} | ${t.data.faultOnly === true ? 'yes' : 'no'} |`),
      '',
    );
  }
}

/**
 * A value in a declaration: expressions and literals as written, objects compactly.
 * @param {any} v
 */
function renderValue(v) {
  if (v === undefined || v === null) return '';
  return text(v);
}

/**
 * Effects of a transition, compactly: `set x = expr` and `emit e after n`.
 * @param {any} effects
 */
function effectsText(effects) {
  return list(effects).map(effectText).join('; ');
}

/** @param {any} e */
function effectText(e) {
  if (!e || typeof e !== 'object' || Array.isArray(e)) return text(e);
  if ('set' in e) return `set ${oneLine(e.set)} = ${oneLine(renderValue(e.to))}`;
  if ('emit' in e) {
    let s = `emit ${oneLine(e.emit)}`;
    if (e.after !== undefined) s += ` after ${oneLine(e.after)}`;
    const payload = e.payload && typeof e.payload === 'object' ? Object.keys(e.payload).sort() : [];
    if (payload.length) s += ` with ${payload.map((k) => `${k} = ${oneLine(renderValue(e.payload[k]))}`).join(', ')}`;
    return s;
  }
  return oneLine(stableStringify(e));
}

/**
 * @param {Model} model
 * @param {{claimResults?: ClaimResult[], diagnostics?: any[], traceability?: any}} [opts]
 * @returns {string} ARCHITECTURE.md text
 */
export function generateArchitectureDoc(model, opts = {}) {
  const hash = semanticHash(model);
  const sys = model.system ?? model.byKind.system?.[0];
  const sd = sys?.data ?? {};
  /** @type {string[]} */
  const L = [];

  L.push(`# ${oneLine(sd.name) || oneLine(sd.id) || 'System'}`, '');
  if (sd.description) L.push(text(sd.description), '');
  L.push(`Generated by Exegra from the semantic model. Semantic hash ${hash}. Do not edit; regenerate.`, '');
  if (sd.illustrative === true) L.push('> This is an illustrative example. It makes no statement about real software.', '');

  const components = model.byKind.component ?? [];
  if (components.length) {
    L.push('## Components', '');
    const seen = new Set();
    /** @param {string|null} parentId @param {number} depth */
    const walk = (parentId, depth) => {
      for (const c of childrenOf(model, parentId)) {
        if (seen.has(c.id)) continue;
        seen.add(c.id);
        L.push(`${'  '.repeat(depth)}- ${oneLine(entityLabel(c))} (\`${oneLine(c.id)}\`, ${categoryLabel(model, c)})`);
        walk(c.id, depth + 1);
      }
    };
    walk(null, 0);
    L.push('');
    for (const c of components) componentSection(model, c, L);
  }

  const relationships = model.byKind.relationship ?? [];
  if (relationships.length) {
    L.push(
      '## Relationships', '',
      '| Id | Kind | From | To | Description |', '| --- | --- | --- | --- | --- |',
      ...relationships.map((r) => `| ${cell(r.id)} | ${cell(r.data.kind)} | ${cell(nameOf(model, r.data.from))} | ${cell(nameOf(model, r.data.to))} | ${cell(r.data.description)} |`),
      '',
    );
  }

  const contracts = model.byKind.contract ?? [];
  if (contracts.length) {
    L.push('## Contracts', '');
    for (const k of contracts) {
      const d = k.data;
      L.push(`### ${oneLine(entityLabel(k))}`, '');
      if (d.description) L.push(text(d.description), '');
      const blocks = [
        ['Inputs', d.inputs], ['Outputs', d.outputs], ['Preconditions', d.preconditions],
        ['Postconditions', d.postconditions], ['Errors', d.errors], ['Obligations', d.obligations],
      ];
      for (const [label, items] of blocks) {
        const xs = list(items);
        if (xs.length) L.push(`#### ${label}`, '', ...xs.map((x) => `- ${itemLine(x)}`), '');
      }
    }
  }

  const behaviors = model.byKind.behavior ?? [];
  if (behaviors.length) {
    L.push('## Behaviors', '');
    for (const b of behaviors) behaviorSection(model, b, L);
  }

  const events = model.byKind.event ?? [];
  if (events.length) {
    L.push(
      '## Events', '',
      '| Id | Name | Payload | Description |', '| --- | --- | --- | --- |',
      ...events.map((e) => `| ${cell(e.id)} | ${cell(entityLabel(e))} | ${cell(list(e.data.payload).map(itemLine).join(', '))} | ${cell(e.data.description)} |`),
      '',
    );
  }

  const faults = model.byKind.fault ?? [];
  if (faults.length) {
    L.push(
      '## Faults', '',
      '| Id | Name | Kind | Event | Transition | Occurrence | By | At | Description |', '| --- | --- | --- | --- | --- | --- | --- | --- | --- |',
      ...faults.map((f) => `| ${cell(f.id)} | ${cell(entityLabel(f))} | ${cell(f.data.kind)} | ${cell(nameOf(model, f.data.event))} | ${cell(nameOf(model, f.data.transition))} | ${cell(f.data.occurrence)} | ${cell(f.data.by)} | ${cell(f.data.at)} | ${cell(f.data.description)} |`),
      '',
    );
  }

  const scenarios = model.byKind.scenario ?? [];
  if (scenarios.length) {
    L.push('## Scenarios', '');
    for (const s of scenarios) {
      const d = s.data;
      L.push(`### ${oneLine(entityLabel(s))}`, '');
      if (d.description) L.push(text(d.description), '');
      const info = [];
      const behaviorNames = list(d.behaviors).map((id) => nameOf(model, id));
      if (behaviorNames.length) info.push(`- Behaviors: ${behaviorNames.join(', ')}`);
      if (d.maxSteps !== undefined) info.push(`- Step limit: ${oneLine(d.maxSteps)}`);
      if (info.length) L.push(...info, '');
      const steps = list(d.steps);
      if (steps.length) {
        L.push(
          '#### Steps', '',
          '| At | Event | Payload | Note |', '| --- | --- | --- | --- |',
          ...steps.map((st) => `| ${cell(st.at)} | ${cell(nameOf(model, st.event))} | ${cell(st.payload)} | ${cell(st.note)} |`),
          '',
        );
      }
      const active = list(d.faults);
      if (active.length) L.push('#### Active faults', '', ...active.map((id) => `- ${nameOf(model, id)} (\`${oneLine(id)}\`)`), '');
    }
  }

  const rows = claimRows(model, opts.claimResults ?? []);
  if (rows.length) {
    L.push(
      '## Claims', '',
      '| Id | Kind | Status | Statement |', '| --- | --- | --- | --- |',
      ...rows.map(({ claim, result }) => `| ${cell(claim.id)} | ${cell(claim.data.kind)} | ${cell(statusLabel(result.status))} | ${cell(claim.data.statement)} |`),
      '',
      `Statuses are evaluation results for semantic hash ${hash}; see claims-report.md for scope and evidence.`, '',
    );
  }

  const assumptions = model.byKind.assumption ?? [];
  if (assumptions.length) {
    L.push('## Assumptions', '');
    for (const a of assumptions) {
      let line = `- \`${oneLine(a.id)}\`: ${oneLine(a.data.statement)}`;
      if (a.data.rationale) line += ` Rationale: ${oneLine(a.data.rationale)}`;
      if (a.data.illustrative === true) line += ' Illustrative.';
      L.push(line);
    }
    L.push('');
  }

  const views = model.byKind.view ?? [];
  if (views.length) {
    L.push(
      '## Views', '',
      '| Id | Name | Projection | Description | Filter | Display |', '| --- | --- | --- | --- | --- | --- |',
      ...views.map((v) => `| ${cell(v.id)} | ${cell(entityLabel(v))} | ${cell(v.data.projection)} | ${cell(v.data.description)} | ${cell(v.data.filter)} | ${cell(v.data.display)} |`),
      '',
    );
  }

  return markdown(L);
}
