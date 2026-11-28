// Compares a one-file specification with a specification (a manifest or a file) as Exegra resolves it (WG-5704).
//
//   node tools/compare-spec.js <before.jsonc> <spec.jsonc>
//
// Prints whether the two documents are JSON-equal, and whether each array section lists its entities in the same
// order. Exits 1 when the documents differ in content. The semantic hash of each is the platform's own:
// `node cli/exegra.js validate --project <name>` prints it.

import fs from 'node:fs';
import path from 'node:path';
import { parse as parseJsonc } from 'jsonc-parser';
import { resolveSpecText } from './spec-manifest.js';

/** @param {any} doc @returns {any} the document with each array section sorted by entity id */
const canonical = (doc) => Object.fromEntries(Object.keys(doc).sort().map((k) => [k, Array.isArray(doc[k]) ? [...doc[k]].sort((a, b) => String(a?.id).localeCompare(String(b?.id))) : doc[k]]));

const [beforeFile, afterFile] = process.argv.slice(2);
if (!beforeFile || !afterFile) {
  console.error('usage: node tools/compare-spec.js <before.jsonc> <spec.jsonc>');
  process.exit(2);
}
const before = parseJsonc(resolveSpecText(path.resolve(beforeFile), fs.readFileSync(beforeFile, 'utf8')).text);
const after = parseJsonc(resolveSpecText(path.resolve(afterFile), fs.readFileSync(afterFile, 'utf8')).text);
const sameSet = JSON.stringify(canonical(before)) === JSON.stringify(canonical(after));
console.log(`JSON-equal (entities of a section compared by id): ${sameSet}`);
console.log(`JSON-equal with every section in the same order: ${JSON.stringify(before) === JSON.stringify(after)}`);
for (const k of Object.keys(before)) {
  if (!Array.isArray(before[k])) continue;
  const same = JSON.stringify(before[k].map((x) => x.id)) === JSON.stringify(after[k]?.map((x) => x.id));
  console.log(`  ${k}: ${before[k].length} entities, ${same ? 'same order' : 'reordered'}`);
}
process.exit(sameSet ? 0 : 1);
