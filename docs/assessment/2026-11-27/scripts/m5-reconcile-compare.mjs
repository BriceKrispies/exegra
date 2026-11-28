// Compare Exegra's extraction with the independent recomputation of the audit (m5-audit-recompute.mjs) on the same
// inputs: a specification (default: the one in the working tree) and the working tree's fact file.
//
//   node docs/assessment/2026-11-27/scripts/m5-reconcile-compare.mjs [--spec <spec.jsonc>]
//
// Exegra's side: the extracted module-level relationships (src/core/extraction.js), lifted to ordered component pairs
// the way the audit lifted import edges (JavaScript files of src/, cli/ and tools/ only: the audit's scope), against the
// ordered pairs of the declared relationships of any kind. Prints both sets as JSON so a diff shows any difference.
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '../../../..');
const args = process.argv.slice(2);
const specPath = path.resolve(args.includes('--spec') ? args[args.indexOf('--spec') + 1] : path.join(root, 'specs/exegra/spec.jsonc'));
const { analyzeSpec } = await import(`file://${root.replace(/\\/g, '/')}/src/core/analyze.js`);
const { attachExtracted, extractionOf } = await import(`file://${root.replace(/\\/g, '/')}/src/core/extraction.js`);
const { componentOf } = await import(`file://${root.replace(/\\/g, '/')}/src/core/query.js`);

const model = analyzeSpec(fs.readFileSync(specPath, 'utf8')).model;
const facts = JSON.parse(fs.readFileSync(path.join(root, 'specs/exegra/extracted/facts.json'), 'utf8'));
// Only JavaScript sources of the audit's scope: drop the other files' imports before attaching.
const scoped = { ...facts, files: facts.files.map((f) => (/^(src|cli|tools)\//.test(f.path) && f.language === 'js' ? f : { ...f, imports: [] })) };
const m = attachExtracted(model, scoped);
const pairs = new Set();
for (const e of extractionOf(m).edges) {
  const a = componentOf(m, e.from)?.id, b = componentOf(m, e.to)?.id;
  if (a && b && a !== b) pairs.add(`${a}>${b}`);
}
const declared = new Set();
for (const r of model.byKind.relationship) {
  const a = componentOf(model, r.data.from)?.id, b = componentOf(model, r.data.to)?.id;
  if (a && b && a !== b) declared.add(`${a}>${b}`);
}
const undeclared = [...pairs].filter((k) => !declared.has(k)).sort();
const reversed = undeclared.filter((k) => { const [a, b] = k.split('>'); return declared.has(`${b}>${a}`); });
const unimported = [...declared].filter((k) => !pairs.has(k)).sort();
const out = { importPairs: pairs.size, declaredPairs: declared.size, undeclaredPairs: undeclared.length, reversedOnly: reversed.length, declaredWithoutImport: unimported.length, undeclared, reversed, unimported };
process.stdout.write(`${JSON.stringify(out, null, 1)}\n`);
void execFileSync;
