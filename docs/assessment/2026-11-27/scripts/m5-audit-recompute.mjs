// An independent recomputation of the derivation audit's comparison of imports with declared relationships
// (docs/assessment/2026-11-27/multiscale.md, section 5.4): it shares no code with Exegra's extractor or core. It reads the
// specification text with jsonc-parser, the files with fs, and extracts imports with its own regular expressions.
//
//   node docs/assessment/2026-11-27/scripts/m5-audit-recompute.mjs [--spec <spec.jsonc>] [--root <repo>] [--all] [--json]
//
// Method of the audit: the files claimed by components' implementation.modules (a path ending in / claims the files
// beneath it; the most specific claim wins), the relative imports between JavaScript files (static, re-export, dynamic),
// lifted to ordered component pairs and compared, pair for pair, with the ordered pairs of every declared relationship
// (ports resolved to their owner components).
import fs from 'node:fs';
import path from 'node:path';
import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const { parse } = require('jsonc-parser');

const args = process.argv.slice(2);
const arg = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const root = path.resolve(arg('--root', process.cwd()));
const spec = parse(fs.readFileSync(path.resolve(arg('--spec', path.join(root, 'specs/exegra/spec.jsonc'))), 'utf8'));

const comps = new Map((spec.components ?? []).map((c) => [c.id, c]));
const ports = new Map();
for (const c of spec.components ?? []) for (const p of c.ports ?? []) ports.set(p.id, c.id);
const compOf = (id) => (comps.has(id) ? id : ports.get(id) ?? null);

// file -> component, most specific claim wins
const claims = [];
for (const c of spec.components ?? []) for (const m of c.implementation?.modules ?? []) claims.push({ c: c.id, m: m.split(String.fromCharCode(92)).join('/') });
const owner = (file) => {
  let best = null, len = -1;
  for (const k of claims) {
    const dir = k.m.endsWith('/');
    if (!(dir ? file.startsWith(k.m) : file === k.m)) continue;
    const l = dir ? k.m.length : Infinity;
    if (l > len) { best = k.c; len = l; }
  }
  return best;
};
const walk = (d, out = []) => {
  for (const e of fs.existsSync(d) ? fs.readdirSync(d, { withFileTypes: true }) : []) {
    if (e.name === 'node_modules') continue;
    const p = path.join(d, e.name);
    e.isDirectory() ? walk(p, out) : out.push(path.relative(root, p).split(String.fromCharCode(92)).join('/'));
  }
  return out;
};
const files = new Set();
for (const k of claims) {
  const abs = path.join(root, k.m);
  if (!fs.existsSync(abs)) continue;
  if (fs.statSync(abs).isDirectory()) walk(abs).forEach((f) => files.add(f)); else files.add(k.m);
}
// The audit read the code of src/, cli/ and tools/; --all adds every other claimed JavaScript file (the tests).
const scope = args.includes('--all') ? () => true : (f) => /^(src|cli|tools)\//.test(f);
const js = [...files].filter((f) => (f.endsWith('.js') || f.endsWith('.mjs')) && scope(f)).sort();

// our own import extraction: strip comments, then three patterns
const strip = (t) => t.replace(/\/\*[\s\S]*?\*\//g, '').split('\n').map((l) => l.replace(/^\s*\/\/.*$/, '')).join('\n');
const specsOf = (t) => {
  const code = strip(t);
  const out = new Set();
  for (const re of [/\bfrom\s*['"]([^'"]+)['"]/g, /\bimport\s*['"]([^'"]+)['"]/g, /\bimport\s*\(\s*['"]([^'"]+)['"]\s*\)/g]) for (const m of code.matchAll(re)) out.add(m[1]);
  return [...out];
};
const resolve = (from, s) => {
  const base = path.posix.normalize(path.posix.join(path.posix.dirname(from), s));
  return [base, `${base}.js`, `${base}/index.js`].find((c) => fs.existsSync(path.join(root, c)) && fs.statSync(path.join(root, c)).isFile()) ?? null;
};
const imports = new Map(); // "A>B" -> [file edges]
let edges = 0;
for (const f of js) {
  const a = owner(f);
  for (const s of specsOf(fs.readFileSync(path.join(root, f), 'utf8'))) {
    if (!s.startsWith('.')) continue;
    const g = resolve(f, s);
    if (!g) continue;
    edges++;
    const b = owner(g);
    if (!a || !b || a === b) continue;
    const k = `${a}>${b}`;
    (imports.get(k) ?? imports.set(k, []).get(k)).push(`${f} -> ${g}`);
  }
}
const declared = new Map();
for (const r of spec.relationships ?? []) {
  const a = compOf(r.from), b = compOf(r.to);
  if (!a || !b || a === b) continue;
  const k = `${a}>${b}`;
  (declared.get(k) ?? declared.set(k, []).get(k)).push(`${r.id}:${r.kind}`);
}
const undeclared = [...imports.keys()].filter((k) => !declared.has(k)).sort();
const reversed = undeclared.filter((k) => { const [a, b] = k.split('>'); return declared.has(`${b}>${a}`); });
const unimported = [...declared.keys()].filter((k) => !imports.has(k)).sort();
const external = (id) => ['external', 'actor'].includes(comps.get(id)?.category) || ['external', 'actor'].includes(comps.get(id)?.kind) || !(comps.get(id)?.implementation?.modules?.length);
const result = {
  files: js.length, importEdges: edges, importPairs: imports.size, declaredPairs: declared.size,
  undeclaredPairs: undeclared.length, reversedOnly: reversed.length, declaredWithoutImport: unimported.length,
  declaredWithoutImportInvolvingExternalOrUnimplemented: unimported.filter((k) => k.split('>').some(external)).length,
  undeclared: undeclared.map((k) => ({ pair: k, edges: imports.get(k) })),
  reversed, unimported,
};
if (args.includes('--json')) process.stdout.write(`${JSON.stringify(result, null, 1)}\n`);
else {
  console.log(JSON.stringify({ ...result, undeclared: undefined, reversed: undefined, unimported: undefined }));
  console.log('undeclared import pairs:'); for (const u of result.undeclared) console.log(`  ${u.pair}  (${u.edges.length}) ${u.edges[0]}`);
  console.log('reversed only:', reversed.join(', '));
}
