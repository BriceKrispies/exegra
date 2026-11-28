// The Markdown importer: parsing and rendering functions on small inline Markdown fixtures.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { parse as parseJsonc } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { createWorkspace } from '../../tools/workspace.js';
import { runCommand } from '../../cli/commands.js';
import {
  Loss, splitRow, collapse, extractMentions, parseRequirements, requirementToClaim,
  parseComponentRows, parseBoundaryRows, parseTerms, splitLines, buildDocumentEntities,
  reconstructMarkdown, coverage, buildSpec, blockText, renderEntity, unfaithfulRendering, parseBullets,
} from '../../tools/import-markdown.js';

const REQS = `# Kernel

## Purity and totality

**KRN-002** A kernel function SHALL return the same output
for the same decision input on every call.
- Status: retired
- Verify: property
- Cases: specifications/04-platform-kernel/cases/invariant-families.md
- Boundary: B-17 \`example-kernel\` decision functions, called by C-2
- Traces: G-1, K-49, D-999
- Depends: KRN-001, KRN-404
- Rationale: Same input, same output.
- Milestone: 1
- Seam: 3
- Priority: high

**KRN-001** The kernel SHALL declare no clock.
- Verify: example
- Boundary: B-17 x
- Traces: G-1
- Milestone: 1
`;

/** id -> kind, as the importer builds it */
const INDEX = new Map([
  ['g-1', 'goal'], ['k-49', 'constraint'], ['b-17', 'boundary'], ['c-2', 'component'],
  ['krn-001', 'claim'], ['krn-002', 'claim'],
]);

test('a requirement block with every key becomes a claim with its properties', () => {
  const loss = new Loss();
  const reqs = parseRequirements(REQS, 'specifications/04-platform-kernel/kernel.md', loss);
  assert.deepEqual(reqs.map((r) => r.id), ['krn-002', 'krn-001']);
  assert.equal(reqs[0].statement, 'A kernel function SHALL return the same output for the same decision input on every call.');
  assert.equal(reqs[0].section, 'Purity and totality');
  assert.equal(reqs[0].line, 5);
  assert.equal(reqs[0].endLine, 16);
  const caseIds = new Map([['specifications/04-platform-kernel/cases/invariant-families.md', 'cases-04-platform-kernel-cases-invariant-families']]);
  const c = requirementToClaim(reqs[0], INDEX, loss, { caseIds });
  assert.equal(c.kind, 'requirement');
  assert.deepEqual(c.evaluate, { method: 'property' });
  assert.equal(c.rationale, 'Same input, same output.');
  assert.equal(c.boundary, 'b-17');
  assert.equal(c.boundaryDetail, '`example-kernel` decision functions, called by C-2');
  assert.deepEqual(c.subjects, ['c-2']);
  assert.equal(c.milestone, 1);
  assert.equal(c.seam, 3);
  assert.deepEqual(c.cases, ['cases-04-platform-kernel-cases-invariant-families'], 'a Cases path resolves to a case table');
  assert.equal(c.casesPath, undefined);
  assert.equal(c.area, '04-platform-kernel');
  assert.equal(c.ref, 'KRN-002');
  assert.equal(c.source, 'specifications/04-platform-kernel/kernel.md:5');
});

test('a Cases path matching no case-table file is reported and kept as a string', () => {
  const loss = new Loss();
  const [r] = parseRequirements(REQS, 'f.md', loss);
  const c = requirementToClaim(r, INDEX, loss, { caseIds: new Map() });
  assert.equal(c.cases, undefined);
  assert.equal(c.casesPath, 'specifications/04-platform-kernel/cases/invariant-families.md');
  assert.equal(loss.kinds.get('Cases path matching no case-table file')?.count, 1);
});

test('a retired requirement is marked, and an unknown key is reported, not dropped', () => {
  const loss = new Loss();
  const [r] = parseRequirements(REQS, 'f.md', loss);
  assert.equal(requirementToClaim(r, INDEX, loss).lifecycle, 'retired');
  assert.equal(loss.kinds.get('unmapped requirement key')?.count, 1);
  const [, active] = parseRequirements(REQS, 'f.md', loss);
  assert.equal(requirementToClaim(active, INDEX, loss).lifecycle, 'active');
});

test('an unresolved trace or dependency is left out of the list and counted', () => {
  const loss = new Loss();
  const [r] = parseRequirements(REQS, 'f.md', loss);
  const c = requirementToClaim(r, INDEX, loss);
  assert.deepEqual(c.traces, ['g-1', 'k-49']);
  assert.deepEqual(c.dependsOn, ['krn-001']);
  assert.equal(loss.kinds.get('unresolved reference (traces)')?.examples[0], 'KRN-002 -> D-999');
  assert.equal(loss.kinds.get('unresolved reference (depends)')?.examples[0], 'KRN-002 -> KRN-404');
});

const WHITEPAPER = `# Example

### Process topology

| ID | Component | Owns | Talks to |
|---|---|---|---|
| C-2 | Control plane (\`example-control\`) | The modules, D-112 | C-9, C-10 and C-9 again, browsers |
| C-9 | PostgreSQL | State | C-2 |
| C-8 | Web origins | Origins | browsers |
| C-99 | Broken | only three cells |

## Boundaries

| ID | Boundary | Kind | Who uses it |
|---|---|---|---|
| B-1 | Player web application | UI (semantic HTML) | players |
`;

test('a components table row yields its fields and the component ids in "Talks to"', () => {
  const loss = new Loss();
  const rows = parseComponentRows(WHITEPAPER, 'wp.md', loss);
  assert.deepEqual(rows.map((r) => r.id), ['c-2', 'c-9', 'c-8']);
  assert.equal(rows[0].name, 'Control plane (`example-control`)', 'inline Markdown is kept');
  assert.equal(rows[0].owns, 'The modules, D-112');
  assert.equal(rows[0].source, 'wp.md:7');
  assert.equal(rows[0].line, 7);
  assert.deepEqual(extractMentions(rows[0].talksTo).ids, ['c-9', 'c-10']);
  assert.deepEqual(extractMentions(rows[2].talksTo).ids, []);
  assert.equal(loss.kinds.get('unparsable component row')?.count, 1);
});

test('a boundary row yields name, kind and users', () => {
  const [b] = parseBoundaryRows(WHITEPAPER, 'wp.md');
  assert.deepEqual(b, { ref: 'B-1', id: 'b-1', name: 'Player web application', interfaceKind: 'UI (semantic HTML)', usedBy: 'players', line: 16, source: 'wp.md:16' });
});

test('small helpers', () => {
  assert.deepEqual(splitRow('| a `x | y` | b \\| c |'), ['a `x | y`', 'b | c']);
  assert.equal(collapse('  a\n  b   c '), 'a b c');
  assert.deepEqual(extractMentions('K-36 to K-38, NG-17, ARC-015, G-1').ranges, ['K-36 to K-38']);
  assert.deepEqual(extractMentions('K-36 to K-38, NG-17, ARC-015, G-1').ids, ['k-36', 'k-38', 'ng-17', 'g-1']);
});

// ---- documents, sections, markers and exact reconstruction ----------------------

const PROSE_FILE = `Text before the first heading.

# Platform kernel

Introductory prose with a table.

| a | b |
|---|---|
| 1 | 2 |

## Purity

**KRN-001** The kernel SHALL declare no clock.
- Verify: example
- Boundary: B-17 x
- Traces: G-1
- Milestone: 1

Prose between two requirements, with a code block:

\`\`\`
# not a heading
\`\`\`

**KRN-002** The kernel SHALL be pure,
and say so.
- Verify: property
- Boundary: B-17 y
- Traces: G-1
- Milestone: 1

### Notes

A trailing paragraph.
`;
const PROSE_PATH = 'specifications/04-platform-kernel/kernel.md';

/** The generated model's shape for one file, as far as reconstruction needs it. */
function modelOf(file, text) {
  const loss = new Loss();
  const reqs = parseRequirements(text, file, loss);
  const lines = splitLines(text);
  const runs = reqs.map((r) => ({ id: r.id, start: r.line, end: r.endLine }));
  const d = buildDocumentEntities(file, text, runs);
  const raw = new Map(reqs.map((r) => [r.id, lines.slice(r.line - 1, r.endLine).join('\n')]));
  return { d, raw, spec: { documents: [d.document], sections: d.sections, caseTables: d.caseTable ? [d.caseTable] : [] } };
}

test('a requirements file with prose becomes sections with markers and rebuilds exactly', () => {
  const { d, spec, raw } = modelOf(PROSE_PATH, PROSE_FILE);
  assert.equal(d.document.role, 'requirements');
  assert.equal(d.document.title, 'Platform kernel');
  assert.deepEqual(d.sections.map((s) => [s.level, s.title]), [[0, ''], [1, 'Platform kernel'], [2, 'Purity'], [3, 'Notes']]);
  assert.equal(d.sections[0].body, 'Text before the first heading.\n\n');
  assert.equal(d.sections[1].parent, undefined);
  assert.equal(d.sections[2].parent, d.sections[1].id);
  assert.equal(d.sections[3].parent, d.sections[2].id);
  assert.ok(d.sections[1].body.includes('| 1 | 2 |'), 'tables stay in the body verbatim');
  assert.ok(d.sections[2].body.includes('# not a heading'), 'a fenced line is not a heading');
  assert.match(d.sections[2].body, /\{\{entity:krn-001\}\}\n\nProse between two requirements/);
  assert.match(d.sections[2].body, /```\n\n\{\{entity:krn-002\}\}\n\n$/);
  assert.equal(d.sectionOf.get('krn-002'), d.sections[2].id);
  assert.ok(!d.sections[2].body.includes('SHALL'), 'requirement lines are only in the entity');
  const rebuilt = reconstructMarkdown(spec, (id) => raw.get(id));
  assert.equal(rebuilt.get(PROSE_PATH), PROSE_FILE);
  assert.equal(coverage(rebuilt, new Map([[PROSE_PATH, PROSE_FILE]])).ok, true);
});

test('coverage names the first differing line and counts differences', () => {
  const { spec, raw } = modelOf(PROSE_PATH, PROSE_FILE);
  const changed = PROSE_FILE.replace('A trailing paragraph.', 'A different paragraph.');
  const cov = coverage(reconstructMarkdown(spec, (id) => raw.get(id)), new Map([[PROSE_PATH, changed]]));
  assert.equal(cov.ok, false);
  assert.equal(cov.files[0].differing, 1);
  assert.equal(cov.files[0].first?.expected, 'A different paragraph.');
  // Line endings and trailing whitespace are normalised.
  assert.equal(coverage(reconstructMarkdown(spec, (id) => raw.get(id)), new Map([[PROSE_PATH, PROSE_FILE.replace(/\n/g, '  \r\n')]])).ok, true);
});

const CASE_PATH = 'specifications/04-platform-kernel/cases/invariant-families.md';
const CASE_FILE = `# Invariant families

Each row is one family.

| Family | Theorem |
|---|---|
| value | V-1 |
| authority | A-1 |

Trailing note.
`;

test('a case-table file becomes a caseTable with columns, row count and the exact body', () => {
  const { d, spec } = modelOf(CASE_PATH, CASE_FILE);
  assert.equal(d.document.role, 'cases');
  assert.equal(d.sections.length, 0);
  assert.equal(d.caseTable?.id, 'cases-04-platform-kernel-cases-invariant-families');
  assert.deepEqual(d.caseTable?.columns, ['Family', 'Theorem']);
  assert.equal(d.caseTable?.rowCount, 2);
  assert.equal(d.caseTable?.body, CASE_FILE);
  assert.equal(d.caseTable?.document, d.document.id);
  assert.equal(reconstructMarkdown(spec).get(CASE_PATH), CASE_FILE);
});

test('glossary entries become terms, wrapped definitions included', () => {
  const glossary = `# Glossary

Intro.

- **Account**: a person's platform identity. It can act
  as a player, a developer, or both.
- **Action mix**: the share of each operation (AGT-043).

Closing prose.
`;
  const lines = splitLines(glossary);
  const terms = parseTerms(lines, 0, lines.length);
  assert.deepEqual(terms.map((t) => t.term), ['Account', 'Action mix']);
  assert.equal(terms[0].definition, 'a person\'s platform identity. It can act as a player, a developer, or both.');
  assert.deepEqual([terms[0].line, terms[0].end], [5, 6]);
  const loss = new Loss();
  parseTerms(['- plain bullet'], 0, 1, loss, 'g.md');
  assert.equal(loss.total, 1);
  // The entries are separate entities; the prose stays in the section body.
  const path = 'specifications/glossary.md';
  const d = buildDocumentEntities(path, glossary, terms.map((t, i) => ({ id: 'term-' + i, start: t.line, end: t.end })));
  assert.equal(d.document.role, 'glossary');
  assert.match(d.sections[0].body, /Intro\.\n\n\{\{entity:term-0\}\}\n\{\{entity:term-1\}\}\n\nClosing prose\./);
  const spec = { documents: [d.document], sections: d.sections, terms: terms.map((t, i) => ({ id: 'term-' + i, term: t.term, definition: t.definition })) };
  const raw = new Map(terms.map((t, i) => ['term-' + i, lines.slice(t.line - 1, t.end).join('\n')]));
  assert.equal(reconstructMarkdown(spec, (id) => raw.get(id)).get(path), glossary);
  // Rendered from the properties alone, the wrapped definition comes out on one line.
  assert.match(reconstructMarkdown(spec).get(path) ?? '', /- \*\*Account\*\*: a person's platform identity\. It can act as a player, a developer, or both\.\n/);
});

// ---- rendering from properties ------------------------------------------------------

test('block text joins wrapped lines and keeps paragraphs and nested items', () => {
  const lines = [
    '**Lead.** Decided by',
    '  the founder.',
    '  - First point, which',
    '    wraps.',
    '  - Second point.',
    '',
    '  A closing paragraph.',
  ];
  assert.equal(blockText(lines, 2), '**Lead.** Decided by the founder.\n- First point, which wraps.\n- Second point.\n\nA closing paragraph.');
  assert.equal(blockText(['**Proves:** it works', 'end to end.', '', '- Builds:', '  - a thing,', '    wrapped;'], 0), '**Proves:** it works end to end.\n\n- Builds:\n  - a thing, wrapped;');
});

test('a decision with sub-points renders as a list item with its sub-points', () => {
  const wp = ['- **D-1** **Rust.** Decided by', '  the founder.', '  - Every component', '    in Rust.', '  - Lean for proofs.'];
  const [d] = parseBullets(wp, 0, wp.length, /^D-\d+$/);
  const e = { ref: d.ref, statement: d.text };
  assert.deepEqual(renderEntity('decisions', e, new Map()), ['- **D-1** **Rust.** Decided by the founder.', '  - Every component in Rust.', '  - Lean for proofs.']);
  assert.equal(unfaithfulRendering('decisions', e, wp.join('\n'), new Map()), null);
  assert.notEqual(unfaithfulRendering('decisions', { ...e, statement: '**Rust.** Decided.' }, wp.join('\n'), new Map()), null, 'a lost word is caught');
});

test('a requirement renders its attributes from its properties, in a fixed order', () => {
  const raw = REQS.split('\n').slice(4, 16).join('\n').replace('- Priority: high', '').trim();
  const byId = new Map([
    ['b-17', { ref: 'B-17' }], ['g-1', { ref: 'G-1' }], ['k-49', { ref: 'K-49' }], ['krn-001', { ref: 'KRN-001' }],
    ['cases-x', { path: 'specifications/04-platform-kernel/cases/invariant-families.md' }],
  ]);
  const c = {
    ref: 'KRN-002', statement: 'A kernel function SHALL return the same output for the same decision input on every call.', lifecycle: 'retired',
    evaluate: { method: 'property' }, cases: ['cases-x'], boundary: 'b-17', boundaryDetail: '`example-kernel` decision functions, called by C-2',
    traces: ['g-1', 'k-49'], dependsOn: ['krn-001'], rationale: 'Same input, same output.', milestone: 1, seam: 3,
  };
  const lines = renderEntity('claims', c, byId);
  assert.equal(lines[0], '**KRN-002** A kernel function SHALL return the same output for the same decision input on every call.');
  assert.deepEqual(lines.slice(1).map((l) => l.split(':')[0]), ['- Status', '- Verify', '- Cases', '- Boundary', '- Traces', '- Depends', '- Rationale', '- Milestone', '- Seam']);
  // The source lists D-999 and KRN-404, which resolve to nothing; the rendering does not have them.
  assert.notEqual(unfaithfulRendering('claims', c, raw, byId), null);
  const resolved = raw.replace('Traces: G-1, K-49, D-999', 'Traces: G-1, K-49').replace('Depends: KRN-001, KRN-404', 'Depends: KRN-001');
  assert.equal(unfaithfulRendering('claims', c, resolved, byId), null, 'attribute order and line wrapping do not matter');
});

// ---- a whole small specification, through an import map ----------------------------------

const FIXTURE = path.resolve(import.meta.dirname, '..', 'fixtures', 'markdown-import');
const FIXTURE_MAP = path.join(FIXTURE, 'import-map.jsonc');
const FIXTURE_SOURCE = path.join(FIXTURE, 'repo');

test('a small Markdown specification imports through its import map, covered and deterministic', () => {
  const { text, counts, cov, unfaithful, ok } = buildSpec({ sourceDir: FIXTURE_SOURCE, mapFile: FIXTURE_MAP });
  const { diagnostics, errorCount } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error').slice(0, 5)));
  assert.equal(counts.components, 2);
  assert.equal(counts.claims, 2);
  assert.equal(counts.documents, 3);
  assert.equal(cov.ok, true);
  assert.deepEqual(unfaithful, []);
  assert.equal(ok, true);
  const value = parseJsonc(text);
  assert.equal(value.system.id, 'widgets', 'the project name comes from the map');
  assert.match(value.system.description, /^A small service that stores widgets/, 'the first paragraph under the mapped title');
  assert.deepEqual(value.components.map((c) => c.category), ['computational', 'storage'], 'categories come from the map');
  assert.equal(buildSpec({ sourceDir: FIXTURE_SOURCE, mapFile: FIXTURE_MAP }).text, text);
  assert.throws(() => buildSpec({ sourceDir: FIXTURE_SOURCE, mapFile: path.join(os.tmpdir(), 'no-such-map.jsonc') }));
});

test('a component the import map does not categorise is refused by name', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-map-'));
  try {
    const map = path.join(dir, 'import-map.jsonc');
    fs.writeFileSync(map, '{ "categories": { "C-1": "logical" } }');
    assert.throws(() => buildSpec({ sourceDir: FIXTURE_SOURCE, mapFile: map }), /no category for: c-2|no category for: C-2/i);
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
});
