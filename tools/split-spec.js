// Splits a one-file specification into a manifest and part files, by the placement table it writes (WG-5704).
//
//   node tools/split-spec.js specs/exegra/spec.jsonc [--out <dir>] [--dry-run]
//
// This is the conversion that made specs/exegra/spec.jsonc a manifest. It reads the one file, places each
// entity with the same rule (`placeEntity` of tools/spec-manifest.js) that `apply` uses for a new entity,
// and writes the manifest (spec.jsonc) and the parts (parts/*.jsonc) beside it. Every comment that sits inside
// an entity, or in front of one, moves with it; a comment in front of a section moves with the section. The
// table below is Exegra's own: the area of each subsystem of the semantic core, and the part of each section.
// Another project would write its own table; the manifest's `specSections` is where it then lives.

import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { parse as parseJsonc } from 'jsonc-parser';
import { placeEntity, scanTopLevel } from './spec-manifest.js';

const P = (/** @type {string} */ n) => `parts/${n}.jsonc`;

// The subsystems of the semantic core, by the area their claims, evidence and structure belong to.
const CORE_AREAS = {
  validation: ['validator', 'integrity-rules', 'parser', 'metamodel', 'expression-language', 'queries', 'data-model', 'reader-pages', 'model-hash', 'stable-serialization', 'hash-binding'],
  derivation: ['semantic-core', 'transactions', 'spec-layers', 'semantic-abstraction', 'change-impact', 'model-derivation', 'derivation-cache', 'self-model-replay'],
  verdicts: ['claim-evaluator', 'claim-strength', 'claim-verdict', 'verdict-boundary', 'machine-coverage', 'metric-claims', 'contract-conformance', 'claim-method-registry'],
  simulation: ['simulation-engine', 'simulation-aspect-registry', 'refinement-checker', 'chaos-aspect', 'load-aspect', 'cost-aspect', 'simulation-contract', 'fault-model', 'deployment-model', 'implementation-refinement', 'resource-model', 'workload-model', 'performance-metrics'],
  formal: ['exhaustive-explorer', 'formal-semantics', 'lts-foundation', 'proof-export', 'lean-call-boundary'],
  generation: ['generation-readiness'],
};
/** @type {Record<string, string>} */
const STRUCTURE_OF_CORE = { validation: 'structure-core-model', derivation: 'structure-core-model', verdicts: 'structure-core-model', simulation: 'structure-core-engines', formal: 'structure-core-engines', generation: 'structure-core-engines' };
// The other top-level subsystems, grouped for claims, evidence and behaviours.
const OTHER_ASSURANCE = { application: 'claims-app-ui', visualization: 'claims-app-ui', 'composition-root': 'claims-app-ui', persistence: 'claims-persistence-agent-tooling', 'agent-interface': 'claims-persistence-agent-tooling', tooling: 'claims-persistence-agent-tooling' };
const BEHAVIOUR_PARTS = { application: 'behaviors-app', visualization: 'behaviors-app', 'composition-root': 'behaviors-app', persistence: 'behaviors-persistence', 'browser-storage': 'behaviors-persistence', 'semantic-core': 'behaviors-core-tools', 'agent-interface': 'behaviors-core-tools', tooling: 'behaviors-core-tools' };
const STRUCTURE_SUBSYSTEMS = ['application', 'visualization', 'persistence', 'agent-interface', 'tooling'];

/** @param {(area: string) => string} partOfArea @returns {Record<string, string>} */
function coreValues(partOfArea) {
  /** @type {Record<string, string>} */
  const v = {};
  for (const [area, ids] of Object.entries(CORE_AREAS)) for (const id of ids) v[id] = P(partOfArea(area));
  return v;
}
const chain = [{ section: 'components', field: 'parent', repeat: true }];

/** The placement table (the manifest's `specSections`). @returns {Record<string, any>} */
export function exegraPlacement() {
  const structure = { ...coreValues((a) => STRUCTURE_OF_CORE[a]), ...Object.fromEntries(STRUCTURE_SUBSYSTEMS.map((s) => [s, P(`structure-${s}`)])) };
  const claimsValues = { ...coreValues((a) => `claims-core-${a}`), ...Object.fromEntries(Object.entries(OTHER_ASSURANCE).map(([k, v]) => [k, P(v)])) };
  // Evidence goes with its claim's part. The generation-readiness subsystem's evidence had a part of its own while test
  // evidence was declared; since it is derived from the tests' markers (WG-5705) that part was empty and is gone.
  const evidenceValues = claimsValues;
  const behaviours = Object.fromEntries(Object.entries(BEHAVIOUR_PARTS).map(([k, v]) => [k, P(v)]));
  const assuranceDefault = P('claims-app-ui');
  return {
    components: { by: 'id', via: chain, values: structure, default: P('structure-top') },
    relationships: { by: 'from', via: chain, values: structure, default: P('structure-top') },
    contracts: P('contracts'),
    events: P('events-faults'),
    faults: P('events-faults'),
    behaviors: { by: 'subject', via: chain, values: behaviours, default: P('behaviors-app') },
    scenarios: P('scenarios'),
    assumptions: P('assumptions'),
    claims: { by: 'subjects', via: chain, values: claimsValues, default: assuranceDefault },
    evidence: { by: 'claim', via: [{ section: 'claims', field: 'subjects' }, ...chain], values: evidenceValues, default: assuranceDefault },
    records: P('records-and-decisions'),
    copies: P('records-and-decisions'),
    decisions: P('records-and-decisions'),
    views: P('views-and-rest'),
    environments: P('views-and-rest'),
    failureModes: P('views-and-rest'),
    faultModels: P('views-and-rest'),
    integrityRules: P('views-and-rest'),
    hierarchies: P('views-and-rest'),
    facets: P('views-and-rest'),
    cuts: P('views-and-rest'),
  };
}

const PART_ORDER = [
  'system', 'structure-top', 'structure-application', 'structure-visualization', 'structure-persistence', 'structure-agent-interface', 'structure-tooling',
  'structure-core-model', 'structure-core-engines', 'contracts', 'events-faults', 'behaviors-app', 'behaviors-persistence', 'behaviors-core-tools', 'scenarios', 'assumptions',
  'claims-core-validation', 'claims-core-derivation', 'claims-core-verdicts', 'claims-core-simulation', 'claims-core-formal', 'claims-core-generation',
  'claims-app-ui', 'claims-persistence-agent-tooling', 'records-and-decisions', 'views-and-rest',
].map(P);

/** @type {Record<string, string>} */
const DESCRIPTIONS = {
  system: 'The system, its vocabulary and the specification version.',
  'structure-top': 'Top-level components (the subsystems, the composition root, external systems and actors) and the relationships from them.',
  'structure-core-model': 'Components and relationships of the semantic core: validation, the model, transactions, layers and derivation.',
  'structure-core-engines': 'Components and relationships of the semantic core: claim verdicts, simulation, the formal core and generation.',
  contracts: 'Contracts.',
  'events-faults': 'Events and faults.',
  scenarios: 'Scenarios.',
  assumptions: 'Assumptions.',
  'claims-core-generation': 'Claims of the generation-readiness subsystem.',
  'records-and-decisions': 'Records, copies and decisions.',
  'views-and-rest': 'Views, environments, failure modes, fault models, integrity rules, hierarchies, facets and cuts.',
};

/** The comment text between two offsets, one line per comment, or ''. @param {string} src @param {number} from @param {number} to */
function commentsBetween(src, from, to) {
  const gap = src.slice(from, to).replace(/^\s*,/, '');
  if (!/\/\/|\/\*/.test(gap)) return '';
  return gap.split('\n').map((l) => l.trim()).filter(Boolean).join('\n');
}

/**
 * @param {string} text the one-file specification
 * @returns {{manifest: string, parts: Map<string, string>, table: Record<string, any>}}
 */
export function splitSpec(text) {
  const top = scanTopLevel(text, 'the specification');
  const table = exegraPlacement();
  const names = PART_ORDER;
  /** @type {Map<string, Map<string, any>>} */
  const indexes = new Map();
  const index = (/** @type {string} */ section) => {
    let found = indexes.get(section);
    if (!found) {
      found = new Map();
      const m = top.members.find((x) => x.key === section);
      for (const it of m?.items ?? []) {
        const e = parseJsonc(top.src.slice(it.start, it.end));
        if (e && typeof e.id === 'string') found.set(e.id, e);
      }
      indexes.set(section, found);
    }
    return found;
  };
  /** @type {Map<string, Map<string, {array: boolean, lead: string, items: string[]}>>} */
  const out = new Map(names.map((n) => [n, new Map()]));
  const slot = (/** @type {string} */ part, /** @type {string} */ key, /** @type {boolean} */ array, /** @type {string} */ lead) => {
    const secs = /** @type {Map<string, any>} */ (out.get(part));
    if (!secs.has(key)) secs.set(key, { array, lead, items: [] });
    return secs.get(key);
  };
  let prevEnd = top.src.indexOf('{') + 1;
  for (const m of top.members) {
    const lead = commentsBetween(top.src, prevEnd, m.keyStart);
    prevEnd = m.end;
    if (m.items === null) {
      slot(P('system'), m.key, false, lead).items.push(top.src.slice(m.start, m.end));
      continue;
    }
    let itemEnd = m.start + 1;
    let first = true;
    for (const it of m.items) {
      const entityText = top.src.slice(it.start, it.end);
      const comment = commentsBetween(top.src, itemEnd, it.start);
      itemEnd = it.end;
      const part = placeEntity(table, names, m.key, parseJsonc(entityText), index);
      if (!part || !names.includes(part)) throw new Error(`no part for a ${m.key} entity (${part})`);
      const s = slot(part, m.key, true, '');
      if (first && lead && !s.lead) s.lead = lead;
      first = false;
      s.items.push(comment ? `${comment.split('\n').join('\n    ')}\n    ${entityText}` : entityText);
    }
    if (m.items.length === 0) slot(P('views-and-rest'), m.key, true, lead);
  }
  /** @type {Map<string, string>} */
  const parts = new Map();
  const header = top.src.slice(0, top.src.indexOf('{')).trim();
  for (const name of names) {
    const secs = /** @type {Map<string, any>} */ (out.get(name));
    if (secs.size === 0) continue;
    const base = path.basename(name, '.jsonc');
    const body = [...secs].map(([key, s]) => `${s.lead ? `  ${s.lead.split('\n').join('\n  ')}\n` : ''}  ${JSON.stringify(key)}: ${s.array ? `[\n${s.items.map((/** @type {string} */ t) => `    ${t}`).join(',\n')}\n  ]` : s.items[0]}`);
    const desc = DESCRIPTIONS[base] ?? `Part of the specification: ${[...secs.keys()].join(', ')}.`;
    parts.set(name, `// ${desc}\n${name === P('system') && header ? `${header}\n` : ''}{\n${body.join(',\n')}\n}\n`);
  }
  const used = names.filter((n) => parts.has(n));
  for (const v of Object.values(table)) {
    const named = typeof v === 'string' ? [v] : [...Object.values(v.values), v.default];
    for (const n of named) if (!parts.has(n)) throw new Error(`the table names an empty part ${n}`);
  }
  const manifest = `// The specification of Exegra, kept as a manifest of part files, one per area (WG-5704). Resolve it with\n// tools/spec-manifest.js. Do not read the parts directly: use \`node cli/exegra.js get|find|refs --project exegra\`.\n// "specSections" says which part \`apply\` writes a new entity of a section to; see docs/model-and-format.md.\n{\n  "specParts": [\n${used.map((n) => `    ${JSON.stringify(n)}`).join(',\n')}\n  ],\n  "specSections": ${JSON.stringify(table, null, 2).replace(/\n/g, '\n  ')}\n}\n`;
  return { manifest, parts, table };
}

/** Count the comments in a JSONC text. @param {string} src */
export function countComments(src) {
  let n = 0;
  for (let i = 0; i < src.length; i += 1) {
    const c = src[i];
    if (c === '"') {
      i += 1;
      while (i < src.length && src[i] !== '"') i += src[i] === '\\' ? 2 : 1;
    } else if (c === '/' && src[i + 1] === '/') {
      n += 1;
      while (i < src.length && src[i] !== '\n') i += 1;
    } else if (c === '/' && src[i + 1] === '*') {
      n += 1;
      i = src.indexOf('*/', i + 2) + 1;
    }
  }
  return n;
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const args = process.argv.slice(2);
  const outIdx = args.indexOf('--out');
  const file = args.find((a, i) => !a.startsWith('--') && (outIdx < 0 || i !== outIdx + 1));
  if (!file) {
    console.error('usage: node tools/split-spec.js <spec.jsonc> [--out <dir>] [--dry-run]');
    process.exit(2);
  }
  const dir = outIdx >= 0 ? path.resolve(args[outIdx + 1]) : path.dirname(path.resolve(file));
  const text = fs.readFileSync(file, 'utf8');
  const { manifest, parts } = splitSpec(text);
  let after = countComments(manifest);
  for (const [name, t] of parts) {
    after += countComments(t);
    console.log(`${String(Buffer.byteLength(t)).padStart(8)}  ${name}`);
  }
  console.log(`comments: ${countComments(text)} before, ${after} after (each part and the manifest add a description line)`);
  if (!args.includes('--dry-run')) {
    for (const [name, t] of parts) {
      fs.mkdirSync(path.dirname(path.join(dir, name)), { recursive: true });
      fs.writeFileSync(path.join(dir, name), t);
    }
    fs.writeFileSync(path.join(dir, 'spec.jsonc'), manifest);
  }
}
