// Every durable store the code writes is modelled in the self-specification as a record or a copy.
//
// The test finds the write sites in src/, cli/ and tools/ (plus index.html and vite.config.js) by
// pattern, assigns each to an entry of STORES below, and requires every entry's locator (a storage
// key, a path or a command) to appear in the text of a record or a copy of specs/exegra/spec.jsonc.
// A new write site fails the test until it is listed here and its store is in the specification;
// an entry whose site has gone fails it too.
//
// What the patterns see: localStorage and sessionStorage setItem, node:fs writeFileSync,
// appendFileSync, fs.writeFile, fs.appendFile and fs.rename, createWriteStream, the workspace
// service's atomicWrite, a browser download through URL.createObjectURL, IndexedDB, a Playwright
// screenshot path, and a --out-dir handed to a subprocess. The storage keys are resolved from the
// literal or the constant the call names, and the project files from WORKSPACE_FILES and
// JOURNAL_REL of tools/workspace.js.
//
// What they cannot see: writes made by subprocesses the tools start (lake writes formal/.lake,
// cargo writes engine/target, Playwright writes test-results, npm and Vite write dist/ and caches;
// only build-engine's --out-dir is caught), writes inside dependencies, a write reached through an
// alias of fs or of a storage object, a key computed without a literal prefix, and in-memory state,
// which is not durable and is modelled separately. A site is matched to its entry by a needle in
// its line or by the function it is declared in, not by what it writes: the locator is the author's
// statement of which store it is.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

const ROOT = fileURLToPath(new URL('../..', import.meta.url));
const SPEC = readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'));

const WRITE = /\b(?:localStorage|sessionStorage)\.setItem\(|\bwriteFileSync\(|\bappendFileSync\(|\bfs\.(?:writeFile|appendFile|rename)\(|\bcreateWriteStream\(|(?<!function )\batomicWrite\(|URL\.createObjectURL\(|\bindexedDB\b|\.screenshot\(\s*\{|'--out-dir'/;

/**
 * Each write site and the store it writes. `needle` must occur in the line, or `fn` must be the
 * function declaration the line is in. `locators` must each appear in a record or a copy.
 * @type {{file: string, needle?: string, fn?: string, locators: string[], store: string}[]}
 */
const STORES = [
  { file: 'src/app/session.js', needle: 'localStorage.setItem(STORE_KEY', locators: ['exegra.session'], store: 'session-preferences' },
  { file: 'src/ui/layout.js', needle: 'localStorage.setItem(STORE_KEY', locators: ['exegra.layout'], store: 'responsive-layout-preferences' },
  { file: 'src/app/main.js', needle: 'sessionStorage.setItem(cameraKey()', locators: ['exegra.camera.'], store: 'camera-memory' },
  { file: 'src/ui/toolbar.js', needle: 'URL.createObjectURL', locators: ['.exegra.json'], store: 'project-bundle' },
  { file: 'cli/commands.js', needle: 'stableStringify(trace', locators: ['trace --out'], store: 'cli-outputs' },
  { file: 'cli/commands.js', needle: 'writeFileSync(dest, text)', locators: ['markdown --out'], store: 'markdown-export' },
  { file: 'cli/commands.js', needle: 'writeFileSync(target, `${JSON.stringify(ops', locators: ['cover --write'], store: 'cli-outputs' },
  { file: 'tools/differential.js', fn: 'saveMismatches', locators: ['test-results/differential/'], store: 'differential-artifacts' },
  { file: 'tools/gen-engine-inputs.js', fn: 'main', locators: ['gen-engine-inputs --out'], store: 'differential-artifacts' },
  { file: 'tools/import-markdown.js', needle: 'writeFileSync(dest, t)', locators: ['--export-md'], store: 'markdown-export' },
  { file: 'tools/import-markdown.js', needle: 'writeFileSync(opts.out', locators: ['tools/import-markdown.js (--out)'], store: 'specification-text' },
  { file: 'tools/import-register.js', needle: 'writeFileSync(args.out, md)', locators: ['tools/import-register.js --render --out'], store: 'markdown-export' },
  { file: 'tools/import-register.js', needle: "writeFileSync(args['export-md']", locators: ['tools/import-register.js --export-md'], store: 'markdown-export' },
  { file: 'tools/import-register.js', needle: 'writeFileSync(outFile, r.text)', locators: ['tools/import-register.js (--out'], store: 'specification-text' },
  { file: 'tools/prove-integrity.js', needle: 'leanProofFile(ex', locators: ['formal/generated/integrity/'], store: 'proof-outputs' },
  { file: 'tools/prove-integrity.js', needle: 'valuesTable(ex)', locators: ['.values.json'], store: 'proof-outputs' },
  { file: 'tools/make-benchmark.js', needle: 'writeFileSync(out', locators: ['specs/benchmark/spec.jsonc'], store: 'specification-text' },
  { file: 'tools/prove.js', fn: 'proveScenario', locators: ['formal/generated/'], store: 'proof-outputs' },
  { file: 'tools/prove.js', fn: 'writeKernelModule', locators: ['formal/Exegra/Proofs/'], store: 'proof-outputs' },
  { file: 'tools/record-goldens.js', needle: 'writeFileSync(w.path', locators: ['tests/conformance/goldens/'], store: 'engine-goldens' },
  { file: 'tools/shot.mjs', needle: '.screenshot(', locators: ['tools/shot.mjs'], store: 'screenshot-images' },
  { file: 'tools/walk-shots.mjs', needle: '.screenshot(', locators: ['tools/walk-shots.mjs'], store: 'screenshot-images' },
  { file: 'tools/walk-shots.mjs', needle: 'writeFileSync(`${base}.json`', locators: ['tools/walk-shots.mjs'], store: 'screenshot-images' },
  { file: 'tools/walk-shots.mjs', needle: "writeFileSync(path.join(OUT, 'summary.json')", locators: ['tools/walk-shots.mjs'], store: 'screenshot-images' },
  { file: 'tools/build-engine.js', needle: "'--out-dir'", locators: ['src/engine/pkg/'], store: 'engine-build-output' },
  { file: 'src/core/derivation-cache.js', needle: 'writeFileSync(tmp', locators: ['<stage>-<key>.entry'], store: 'derivation-cache-entry' },
  { file: 'tools/build-formal-wasm.js', fn: 'writeAtomic', locators: ['src/engine/lean/', 'formal-wasm'], store: 'formal-wasm-build-output' },
  { file: 'tools/build-formal-wasm.js', needle: 'writeFileSync(marker', locators: ['.exegra-patches'], store: 'formal-wasm-build-output' },
  { file: 'tools/build-formal-wasm.js', needle: 'writeFileSync(stamp', locators: ['stamp files'], store: 'formal-wasm-build-output' },
  { file: 'tools/build-formal-wasm.js', needle: "'.exegra-patches'", locators: ['.exegra-patches'], store: 'formal-wasm-build-output' },
  { file: 'tools/build-formal-wasm.js', needle: 'writeFileSync(rsp', locators: ['linker response files'], store: 'formal-wasm-build-output' },
  { file: 'tools/outcomes-playwright-reporter.js', needle: 'writeFileSync(OUTPUT', locators: ['.outcomes/playwright.json'], store: 'test-outcomes-file' },
  { file: 'tools/trace-reads.js', needle: 'writeFileSync(path.join(dir', locators: ['tools/trace-reads.js'], store: 'test-outcomes-file' },
  { file: 'cli/commands.js', needle: 'writeFileSync(file, `${JSON.stringify(link', locators: ['exegra project register'], store: 'project-pointer' },
  { file: 'tools/split-spec.js', needle: 'writeFileSync(path.join(dir, name), t)', locators: ['tools/split-spec.js'], store: 'specification-text' },
  { file: 'tools/split-spec.js', needle: "writeFileSync(path.join(dir, 'spec.jsonc'), manifest)", locators: ['tools/split-spec.js'], store: 'specification-text' },
  { file: 'tools/extract.js', needle: 'writeFileSync(out, factsText(facts))', locators: ['specs/<project>/extracted/facts.json', 'tools/extract.js'], store: 'extracted-facts' },
  { file: 'cli/commands.js', needle: 'writeFileSync(target, factsText(facts))', locators: ['exegra extract (cli/commands.js)'], store: 'extracted-facts' },
  { file: 'tools/observe.js', needle: 'fs.writeFileSync(out, text)', locators: ['tools/observe.js --out'], store: 'extracted-facts' },
  { file: 'tools/spec-store.js', needle: 'writeFileSync(tmp, bytes)', locators: ['tools/spec-store.js (store export'], store: 'specification-text' },
  { file: 'tools/spec-store.js', needle: 'writeFileSync(t, part.text', locators: ['tools/spec-store.js (store export', 'part files'], store: 'specification-text' },
  { file: 'tools/lean-theorems.js', needle: 'writeFileSync(file, text)', locators: ['exegra-theorems-'], store: 'lean-theorem-check-file' },
  { file: 'tools/workspace.js', fn: 'atomicWrite', locators: ['atomicWrite'], store: 'write-journal (the replace that precedes the journal line)' },
  { file: 'tools/workspace.js', fn: 'write', locators: ['spec.jsonc', 'layout.jsonc', '.history/journal.jsonl'], store: 'specification-text, presentation-layout, write-journal' },
  { file: 'tools/workspace.js', fn: 'writeGenerated', locators: ['specs/<project>/generated/'], store: 'generated-documents' },
  { file: 'tools/workspace.js', fn: 'writeRecorded', locators: ['evidence/results.json'], store: 'recorded-results' },
  { file: 'tools/workspace.js', fn: 'writeSpecText', locators: ['writeSpecText', 'part files'], store: 'specification-text (the part files of a manifest)' },
  { file: 'tools/workspace.js', fn: 'importProject', locators: ['importProject'], store: 'specification-text (bundle import)' },
];

/** @param {string} dir @returns {string[]} */
function sources(dir) {
  const out = [];
  for (const name of readdirSync(path.join(ROOT, dir))) {
    const rel = `${dir}/${name}`;
    if (rel === 'src/engine/pkg') continue; // generated by tools/build-engine.js
    if (statSync(path.join(ROOT, rel)).isDirectory()) out.push(...sources(rel));
    else if (/\.(m?js|html)$/.test(name)) out.push(rel);
  }
  return out;
}

const FILES = [...sources('src'), ...sources('cli'), ...sources('tools'), 'index.html', 'vite.config.js'];
const TEXT = new Map(FILES.map((f) => [f, readFileSync(path.join(ROOT, f), 'utf8')]));

/** The write sites: file, 1-based line, the line, and the function declaration it is in. */
function writeSites() {
  const sites = [];
  for (const [file, text] of TEXT) {
    const lines = text.split(/\r?\n/);
    let fn = null;
    lines.forEach((line, i) => {
      const decl = /^\s*(?:export\s+)?(?:async\s+)?function\s+(\w+)/.exec(line);
      if (decl) fn = decl[1];
      if (WRITE.test(line) && !/^\s*(\/\/|\*)/.test(line)) sites.push({ file, line: i + 1, text: line.trim(), fn });
    });
  }
  return sites;
}

/** The text of every record and copy of the self-specification. */
function dataModelText() {
  const { model, diagnostics } = analyzeSpec(SPEC);
  assert.ok(model, `the self-specification parses: ${diagnostics[0]?.message}`);
  const entities = [...(model.byKind.record ?? []), ...(model.byKind.copy ?? [])];
  return entities.map((e) => ({ id: e.id, kind: e.kind, text: JSON.stringify(e.data) }));
}

// Every write site found by pattern in src/, cli/ and tools/ belongs to exactly one listed store and every listed store still has a site; each store's locator, every browser storage key the code writes and every workspace project file appear in a record or a copy of specs/exegra/spec.jsonc. A new write site, key or project file fails it until its store is modelled.
// @evidence runtime-stores-modelled #
test('every write site in the code belongs to exactly one listed store, and every listed store has a site', () => {
  const sites = writeSites();
  const used = new Set();
  const unmatched = [];
  for (const s of sites) {
    const hits = STORES.filter((e) => e.file === s.file && (e.needle ? s.text.includes(e.needle) : s.fn === e.fn));
    if (hits.length !== 1) unmatched.push(`${s.file}:${s.line} (${hits.length} entries) ${s.text}`);
    for (const h of hits) used.add(h);
  }
  assert.deepEqual(unmatched, [], 'write sites with no store, or with more than one: list each in STORES and model its store as a record or a copy');
  const stale = STORES.filter((e) => !used.has(e)).map((e) => `${e.file} ${e.needle ?? e.fn}`);
  assert.deepEqual(stale, [], 'STORES entries whose write site no longer exists');
});

test('every listed store is named by a record or a copy of the self-specification', () => {
  const data = dataModelText();
  const missing = [];
  for (const e of STORES) for (const loc of e.locators) if (!data.some((d) => d.text.includes(loc))) missing.push(`${loc} (${e.file}, ${e.store})`);
  assert.deepEqual(missing, [], 'stores the code writes that no record or copy names');
});

test('every browser storage key the code writes is named by a record or a copy', () => {
  const data = dataModelText();
  const keys = [];
  for (const [file, text] of TEXT) {
    for (const m of text.matchAll(/\b(?:localStorage|sessionStorage)\.setItem\(\s*([^,]+),/g)) {
      const arg = m[1].trim();
      let key = null;
      const lit = /^['"`]([^'"`$]*)/.exec(arg);
      if (lit) key = lit[1];
      else {
        const name = /^(\w+)/.exec(arg)?.[1];
        const def = name && new RegExp(`(?:const|let)\\s+${name}\\s*=\\s*(?:\\([^)]*\\)\\s*=>\\s*)?['"\`]([^'"\`$]*)`).exec(text);
        key = def ? def[1] : null;
      }
      assert.ok(key, `${file}: the storage key ${arg} has no literal or literal prefix the test can read`);
      keys.push({ file, key });
    }
  }
  assert.ok(keys.length >= 3, 'the session, layout and camera keys are found');
  const missing = keys.filter(({ key }) => !data.some((d) => d.text.includes(key))).map(({ file, key }) => `${key} (${file})`);
  assert.deepEqual(missing, [], 'browser storage keys that no record or copy names');
});

test('every project file the workspace service writes is named by a record or a copy', () => {
  const data = dataModelText();
  const ws = TEXT.get('tools/workspace.js') ?? '';
  const block = /WORKSPACE_FILES\s*=\s*\{([^}]*)\}/.exec(ws)?.[1] ?? '';
  const files = [...block.matchAll(/:\s*'([^']+)'/g)].map((m) => m[1]);
  const journal = /JOURNAL_REL\s*=\s*'([^']+)'/.exec(ws)?.[1];
  assert.deepEqual(files, ['spec.jsonc', 'layout.jsonc', 'evidence/results.json']);
  assert.ok(journal, 'JOURNAL_REL is found');
  const missing = [...files, journal, 'generated/'].filter((f) => !data.some((d) => d.text.includes(f)));
  assert.deepEqual(missing, [], 'project files that no record or copy names');
});
