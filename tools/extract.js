// The static extractor (WG-5696, M5). Node-only: it reads the file system, so it lives outside the browser-safe
// core (docs/module-contracts.md). It reads every file of the implementation surface (tools/surface.js) and writes
// the facts a reader of the code can state without running it:
//
//   files    every surface file with its sha-256 digest, so a fact is a function of the bytes it was read from;
//   imports  per JavaScript file the static imports (`import ... from`, `import 'x'`), re-exports (`export ... from`),
//            dynamic imports (`import('x')`, marked `dynamic`), `require()` and builtin references, each with the
//            specifier and, for a relative one, the resolved repo-relative file; per Lean file its `import` lines;
//            per Rust file its module-level `mod x;` and `use` paths.
//
// Module granularity is the floor: no symbol, function or call is extracted. Static extraction establishes static
// structure only. It never establishes runtime behaviour, and nothing downstream may present it as such.
//
// The extractor is a trusted component (its soundness, that it reports exactly the static imports of the files it
// reads, is not provable in Lean); tests/core/extract.test.js checks it against a corpus. Its output is data: the
// core reads it as facts with provenance `extracted` (src/core/extraction.js).

import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { scanSurface, slash } from './surface.js';

/** The identity and version stamped on every fact file. Bump the version whenever extraction logic changes. */
export const EXTRACTOR = { id: 'exegra-static-extractor', version: '2' };
/** The format of the fact file (src/core/extraction.js validates it). */
export const FACTS_FORMAT = 'exegra-extracted-facts/1';
/** Where the fact file of this repository lives, relative to the repository root. */
export const FACTS_PATH = 'specs/exegra/extracted/facts.json';

/**
 * The digest of a file's content. Line endings are normalised first (CRLF to LF), so a checkout with another
 * newline convention gives the same digest and the same facts.
 * @param {Buffer|string} bytes
 */
export const digestOf = (bytes) => `sha256:${createHash('sha256').update(bytes.toString('utf8').split(String.fromCharCode(13, 10)).join(String.fromCharCode(10))).digest('hex')}`;

// ---------------------------------------------------------------------------------------------
// JavaScript

/** Remove comments, leaving string contents (an import written in a comment is not an import). @param {string} text */
export function stripComments(text) {
  return text.replace(/\/\*[\s\S]*?\*\//g, '').replace(/(^|[^:'"`\\])\/\/[^\n]*/g, '$1');
}

/** @typedef {'static'|'reexport'|'dynamic'|'require'|'builtin'} ImportHow */

const JS_PATTERNS = /** @type {[RegExp, ImportHow][]} */ ([
  [/\bimport\s+(?:[^'";]*?\s+from\s+)?['"]([^'"]+)['"]/g, 'static'],
  [/\bexport\s+[^'";]*?\s+from\s+['"]([^'"]+)['"]/g, 'reexport'],
  [/\bimport\s*\(\s*['"]([^'"]+)['"]\s*\)/g, 'dynamic'],
  [/\brequire\s*\(\s*['"]([^'"]+)['"]\s*\)/g, 'require'],
  [/\bgetBuiltinModule\s*\(\s*['"]([^'"]+)['"]\s*\)/g, 'builtin'],
  // a node: builtin named anywhere in the code, as when it is handed to a helper that calls getBuiltinModule
  [/['"](node:[a-z_/]+)['"]/g, 'builtin'],
]);

/**
 * The module specifiers of JavaScript source, with how each is reached, in order of first appearance (a specifier
 * reached several ways keeps its first way, and the strongest static one wins over a mere builtin mention).
 * @param {string} text
 * @returns {{spec: string, how: ImportHow}[]}
 */
export function jsImports(text) {
  const code = stripComments(text);
  /** @type {{at: number, spec: string, how: ImportHow}[]} */
  const found = [];
  for (const [re, how] of JS_PATTERNS) for (const m of code.matchAll(re)) found.push({ at: m.index ?? 0, spec: m[1], how });
  found.sort((a, b) => a.at - b.at);
  /** @type {Map<string, ImportHow>} */
  const first = new Map();
  const rank = { static: 0, reexport: 0, require: 1, dynamic: 2, builtin: 3 };
  for (const f of found) {
    const prior = first.get(f.spec);
    if (prior === undefined || rank[f.how] < rank[prior]) first.set(f.spec, f.how);
  }
  return [...first].map(([spec, how]) => ({ spec, how }));
}

/**
 * Resolve a relative JavaScript specifier from `file` to a repo-relative file that exists, or null.
 * @param {string} repoRoot @param {string} file @param {string} spec
 */
function resolveRelative(repoRoot, file, spec) {
  const base = slash(path.posix.normalize(path.posix.join(path.posix.dirname(file), spec)));
  for (const candidate of [base, `${base}.js`, `${base}/index.js`]) {
    try {
      if (fs.statSync(path.join(repoRoot, candidate)).isFile()) return candidate;
    } catch { /* not there */ }
  }
  return null;
}

/**
 * @typedef {{spec: string, how: ImportHow|'import'|'mod'|'use', resolved: string|null, external: boolean}} ImportFact
 */

/** @param {string} repoRoot @param {string} file @param {string} text @returns {ImportFact[]} */
function jsFacts(repoRoot, file, text) {
  return jsImports(text).map(({ spec, how }) => {
    if (spec.startsWith('.')) return { spec, how, resolved: resolveRelative(repoRoot, file, spec), external: false };
    return { spec, how, resolved: null, external: true };
  });
}

// ---------------------------------------------------------------------------------------------
// Lean

/** @param {string} repoRoot @param {string} text @returns {ImportFact[]} */
function leanFacts(repoRoot, text) {
  const out = [];
  for (const m of text.replace(/\/-[\s\S]*?-\//g, '').replace(/--[^\n]*/g, '').matchAll(/^\s*(?:public\s+|meta\s+)?import\s+([A-Za-z0-9_.]+)/gm)) {
    const spec = m[1];
    const rel = `formal/${spec.split('.').join('/')}.lean`;
    const exists = fs.existsSync(path.join(repoRoot, rel));
    out.push({ spec, how: /** @type {'import'} */ ('import'), resolved: exists ? rel : null, external: !exists });
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// Rust

/**
 * The crates of the repository: package name (hyphens as underscores) to the repo-relative src directory.
 * @param {string} repoRoot @returns {Map<string, string>}
 */
function rustCrates(repoRoot) {
  /** @type {Map<string, string>} */
  const out = new Map();
  /** @param {string} dir */
  const visit = (dir) => {
    let entries;
    try { entries = fs.readdirSync(path.join(repoRoot, dir), { withFileTypes: true }); } catch { return; }
    for (const e of entries) {
      if (e.name === 'target' || e.name === 'node_modules') continue;
      if (e.isDirectory()) visit(`${dir}/${e.name}`);
      else if (e.name === 'Cargo.toml') {
        const text = fs.readFileSync(path.join(repoRoot, dir, e.name), 'utf8');
        const pkg = /\[package\][\s\S]*?\bname\s*=\s*"([^"]+)"/.exec(text);
        if (pkg && fs.existsSync(path.join(repoRoot, dir, 'src'))) out.set(pkg[1].replace(/-/g, '_'), `${dir}/src`);
      }
    }
  };
  visit('engine');
  return out;
}

/** Expand `a::{b, c::d}` into whole paths. @param {string} tree @returns {string[]} */
function expandUse(tree) {
  const t = tree.replace(/\s+/g, '');
  const brace = t.indexOf('{');
  if (brace < 0) return [t.replace(/::\*$/, '').replace(/\bas\w+$/, '')].filter(Boolean);
  const prefix = t.slice(0, brace).replace(/::$/, '');
  const close = t.lastIndexOf('}');
  const inner = t.slice(brace + 1, close);
  /** @type {string[]} */
  const parts = [];
  let depth = 0, cur = '';
  for (const ch of inner) {
    if (ch === '{') depth++;
    if (ch === '}') depth--;
    if (ch === ',' && depth === 0) { parts.push(cur); cur = ''; } else cur += ch;
  }
  if (cur) parts.push(cur);
  return parts.flatMap((p) => expandUse(prefix ? `${prefix}::${p}` : p).map((x) => x));
}

/**
 * The module file a path of segments names inside one crate, longest prefix first.
 * @param {string} repoRoot @param {string} srcDir @param {string[]} segments
 */
function rustModuleFile(repoRoot, srcDir, segments) {
  for (let n = segments.length; n >= 1; n--) {
    const rel = segments.slice(0, n).join('/');
    for (const candidate of [`${srcDir}/${rel}.rs`, `${srcDir}/${rel}/mod.rs`]) {
      if (fs.existsSync(path.join(repoRoot, candidate))) return candidate;
    }
  }
  return null;
}

/** @param {string} repoRoot @param {string} file @param {string} text @param {Map<string, string>} crates @returns {ImportFact[]} */
function rustFacts(repoRoot, file, text, crates) {
  const code = stripComments(text);
  /** @type {ImportFact[]} */
  const out = [];
  const dir = path.posix.dirname(file);
  const stem = path.posix.basename(file, '.rs');
  const own = ['lib', 'main', 'mod'].includes(stem) ? dir : `${dir}/${stem}`;
  const srcDir = [...crates.values()].find((d) => file.startsWith(`${d}/`)) ?? dir;
  for (const m of code.matchAll(/^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+([A-Za-z0-9_]+)\s*;/gm)) {
    const name = m[1];
    const resolved = [`${own}/${name}.rs`, `${own}/${name}/mod.rs`].find((c) => fs.existsSync(path.join(repoRoot, c))) ?? null;
    out.push({ spec: name, how: 'mod', resolved, external: resolved === null });
  }
  for (const m of code.matchAll(/^\s*(?:pub(?:\([^)]*\))?\s+)?use\s+([^;]+);/gm)) {
    for (const p of expandUse(m[1])) {
      const segs = p.split('::');
      /** @type {string|null} */
      let resolved = null;
      if (segs[0] === 'crate') resolved = rustModuleFile(repoRoot, srcDir, segs.slice(1));
      else if (segs[0] === 'self') resolved = rustModuleFile(repoRoot, own, segs.slice(1));
      else if (segs[0] === 'super') resolved = rustModuleFile(repoRoot, path.posix.dirname(own), segs.slice(1));
      else if (crates.has(segs[0])) resolved = rustModuleFile(repoRoot, /** @type {string} */ (crates.get(segs[0])), segs.slice(1)) ?? `${crates.get(segs[0])}/lib.rs`;
      out.push({ spec: p, how: 'use', resolved: resolved && resolved !== file ? resolved : null, external: resolved === null && !['crate', 'self', 'super'].includes(segs[0]) && !crates.has(segs[0]) });
    }
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// Claim markers of tests (WG-5705)
//
// A test names the claims it evidences with a line comment the test runner ignores and the extractor reads:
//
//   // @evidence claim-a claim-b               directly above a test(...) or it(...) call with a literal title (more
//                                              marker or comment lines may come between): the reference file#title
//   // @evidence claim-a # <title pattern>     anywhere: the reference file#<pattern>, for titles built at run time
//   // @evidence claim-a #                     anywhere: the whole file
//
// The reference is what `exegra verify` runs (cli/test-batch.js), so the runner and verify read the same tests.
// Each (claim, reference) becomes an evidence entity of the model (src/core/extraction.js, derivedEvidence).

/** The directories whose test files carry claim markers. */
export const TEST_DIRS = ['tests/core', 'tests/proofs', 'tests/browser'];
const TEST_FILE = /\.(test|spec)\.js$/;
const MARKER = /^\s*\/\/\s*@evidence\b(.*)$/;
const TEST_CALL = /^\s*(?:test|it)(?:\.(?:only|skip|fixme|slow|fail|serial))*\s*\(\s*(['"`])/;

/**
 * The claim markers of one test file's text.
 * @param {string} file repo-relative @param {string} text
 * @returns {{evidence: {claim: string, ref: string, file: string, line: number}[], problems: {file: string, line: number, message: string}[]}}
 */
export function markersOf(file, text) {
  const lines = text.split(/\r?\n/);
  /** @type {{claim: string, ref: string, file: string, line: number}[]} */
  const evidence = [];
  /** @type {{file: string, line: number, message: string}[]} */
  const problems = [];
  lines.forEach((l, i) => {
    const m = MARKER.exec(l);
    if (!m) return;
    const body = m[1];
    const hash = body.indexOf('#');
    const ids = (hash < 0 ? body : body.slice(0, hash)).trim().split(/[\s,]+/).filter(Boolean);
    if (!ids.length) { problems.push({ file, line: i + 1, message: 'an @evidence marker names no claim.' }); return; }
    const bad = ids.filter((id) => !/^[a-z0-9][a-z0-9-]*$/.test(id));
    if (bad.length) { problems.push({ file, line: i + 1, message: `an @evidence marker names ${bad.map((b) => `"${b}"`).join(', ')}, which is not a claim id.` }); return; }
    /** @type {string|null} */
    let ref = null;
    if (hash >= 0) {
      const pattern = body.slice(hash + 1).trim();
      ref = pattern ? `${file}#${pattern}` : file;
    } else {
      // The next line that is not a comment must start a test with a literal title.
      let j = i + 1;
      while (j < lines.length && /^\s*\/\//.test(lines[j])) j++;
      const call = j < lines.length ? TEST_CALL.exec(lines[j]) : null;
      if (!call) { problems.push({ file, line: i + 1, message: 'an @evidence marker without "#" must stand directly above a test(...) or it(...) call with a literal title; give the title pattern after "#" otherwise.' }); return; }
      const q = call[1];
      let k = (call.index ?? 0) + call[0].length;
      let title = '';
      const src = lines[j];
      while (k < src.length && src[k] !== q) {
        if (src[k] === '\\') { title += src[k + 1] ?? ''; k += 2; continue; }
        if (q === '`' && src[k] === '$' && src[k + 1] === '{') { title = ''; k = -1; break; }
        title += src[k];
        k++;
      }
      if (k < 0 || k >= src.length) { problems.push({ file, line: i + 1, message: 'the test below this @evidence marker has a title built at run time or spread over lines; give the title pattern after "#".' }); return; }
      ref = `${file}#${title}`;
    }
    for (const claim of ids) evidence.push({ claim, ref, file, line: i + 1 });
  });
  return { evidence, problems };
}

/**
 * Every test file's claim markers, in file order then line order. Deterministic.
 * @param {string} repoRoot
 */
export function testEvidence(repoRoot) {
  /** @type {string[]} */
  const files = [];
  const walk = (/** @type {string} */ rel) => {
    let entries;
    try { entries = fs.readdirSync(path.join(repoRoot, rel), { withFileTypes: true }); } catch { return; }
    for (const e of entries) {
      const child = `${rel}/${e.name}`;
      if (e.isDirectory()) { if (e.name !== 'fixtures' && e.name !== 'node_modules') walk(child); }
      else if (TEST_FILE.test(e.name)) files.push(child);
    }
  };
  for (const d of TEST_DIRS) walk(d);
  files.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  /** @type {ReturnType<typeof markersOf>} */
  const all = { evidence: [], problems: [] };
  for (const f of files) {
    const r = markersOf(f, fs.readFileSync(path.join(repoRoot, f), 'utf8'));
    all.evidence.push(...r.evidence);
    all.problems.push(...r.problems);
  }
  return all;
}

// ---------------------------------------------------------------------------------------------
// The fact file

/**
 * @typedef {{path: string, language: string, digest: string, imports: ImportFact[]}} FileFact
 * @typedef {{format: string, provenance: 'extracted', extractor: {id: string, version: string}, files: FileFact[], evidence?: {claim: string, ref: string, file: string, line: number}[], evidenceProblems?: {file: string, line: number, message: string}[]}} Facts
 */

const LANGUAGE = { '.js': 'js', '.lean': 'lean', '.rs': 'rust', '.json': 'json', '.css': 'css', '.html': 'html' };

/**
 * The facts of one file.
 * @param {string} repoRoot @param {string} file repo-relative @param {Map<string, string>} crates
 * @returns {FileFact}
 */
export function extractFile(repoRoot, file, crates = rustCrates(repoRoot)) {
  const bytes = fs.readFileSync(path.join(repoRoot, file));
  const language = /** @type {Record<string, string>} */ (LANGUAGE)[path.extname(file)] ?? 'other';
  const text = bytes.toString('utf8');
  const imports = language === 'js' ? jsFacts(repoRoot, file, text)
    : language === 'lean' ? leanFacts(repoRoot, text)
    : language === 'rust' ? rustFacts(repoRoot, file, text, crates) : [];
  return { path: file, language, digest: digestOf(bytes), imports };
}

/**
 * Extract the facts of every file of the surface, or of `files` when given. Deterministic: sorted by path, no clock.
 * @param {string} repoRoot @param {{files?: string[]}} [opts]
 * @returns {Facts}
 */
export function extractRepository(repoRoot, opts = {}) {
  const crates = rustCrates(repoRoot);
  const files = (opts.files ?? scanSurface(repoRoot)).map(slash).sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  /** @type {Facts} */
  const facts = { format: FACTS_FORMAT, provenance: /** @type {const} */ ('extracted'), extractor: { ...EXTRACTOR }, files: files.map((f) => extractFile(repoRoot, f, crates)) };
  if (opts.files) return facts;
  const markers = testEvidence(repoRoot);
  return { ...facts, evidence: markers.evidence, ...(markers.problems.length ? { evidenceProblems: markers.problems } : {}) };
}

/**
 * Compare a stored fact file with the tree: the files whose digest differs, the files the tree has and the facts
 * lack, and the facts of files the tree no longer has. An empty result means the facts describe the tree.
 * @param {Facts} stored @param {string} repoRoot
 * `evidence` is true when the claim markers of the tests differ from those the facts record.
 * @returns {{changed: string[], missing: string[], gone: string[], extractor: boolean, evidence: boolean}}
 */
export function factsDrift(stored, repoRoot) {
  const have = new Map(stored.files.map((f) => [f.path, f.digest]));
  const surface = scanSurface(repoRoot);
  const changed = [], missing = [];
  for (const f of surface) {
    if (!have.has(f)) { missing.push(f); continue; }
    if (digestOf(fs.readFileSync(path.join(repoRoot, f))) !== have.get(f)) changed.push(f);
  }
  const live = new Set(surface);
  const markers = testEvidence(repoRoot);
  const evidence = JSON.stringify(stored.evidence ?? []) !== JSON.stringify(markers.evidence) || JSON.stringify(stored.evidenceProblems ?? []) !== JSON.stringify(markers.problems);
  return { changed, missing, gone: [...have.keys()].filter((f) => !live.has(f)), extractor: stored.extractor?.version !== EXTRACTOR.version || stored.extractor?.id !== EXTRACTOR.id, evidence };
}

/** The fact file as text: stable key order, one file per block. @param {Facts} facts */
export function factsText(facts) {
  return `${JSON.stringify(facts, null, 1)}\n`;
}

/** Read a fact file, or null when there is none. @param {string} file @returns {Facts|null} */
export function readFacts(file) {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return null; }
}

// Run as a command: `node tools/extract.js [--out <file>] [--root <dir>] [--check]`.
if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, '$1'))) {
  const args = process.argv.slice(2);
  const arg = (/** @type {string} */ name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
  const root = path.resolve(arg('--root') ?? path.join(path.dirname(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, '$1')), '..'));
  const out = path.resolve(root, arg('--out') ?? FACTS_PATH);
  if (args.includes('--check')) {
    const stored = readFacts(out);
    const drift = stored ? factsDrift(stored, root) : null;
    const ok = !!drift && !drift.changed.length && !drift.missing.length && !drift.gone.length && !drift.extractor && !drift.evidence;
    process.stdout.write(`${JSON.stringify({ ok, drift })}\n`);
    process.exit(ok ? 0 : 1);
  }
  const facts = extractRepository(root);
  fs.mkdirSync(path.dirname(out), { recursive: true });
  fs.writeFileSync(out, factsText(facts));
  process.stdout.write(`${JSON.stringify({ wrote: slash(path.relative(root, out)), files: facts.files.length, imports: facts.files.reduce((n, f) => n + f.imports.length, 0) })}\n`);
}
