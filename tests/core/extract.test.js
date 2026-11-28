// The static extractor (tools/extract.js, WG-5696): a corpus of JavaScript, Lean and Rust sources, determinism by file
// bytes, digest stability, and the committed fact file of this repository against the tree.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { jsImports, extractRepository, extractFile, factsDrift, readFacts, digestOf, FACTS_PATH, EXTRACTOR } from '../../tools/extract.js';
import { checkFacts } from '../../src/core/extraction.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

/** A temporary repository with the given files. @param {Record<string, string>} files */
function repoWith(files) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-extract-'));
  for (const [rel, text] of Object.entries(files)) {
    fs.mkdirSync(path.dirname(path.join(dir, rel)), { recursive: true });
    fs.writeFileSync(path.join(dir, rel), text);
  }
  return dir;
}

// The extractor reads a corpus of JavaScript, Lean and Rust sources and the repository itself, and its facts depend on the bytes only.
// @evidence static-extractor-reads-exact-imports #
test('JavaScript: static imports, re-exports, dynamic imports, require and builtins are told apart, comments ignored', () => {
  const text = [
    "import fs from 'node:fs';",
    "import { a } from './a.js';",
    "import './side.js';",
    "export { c } from '../c.js';",
    "export * from './star.js';",
    "const m = await import('./lazy.js');",
    "const r = require('pkg');",
    "const p = process.getBuiltinModule('node:path');",
    "// import x from './commented.js';",
    "/* import y from './blocked.js'; */",
    "const url = 'https://example.org/x.js';",
  ].join('\n');
  const got = Object.fromEntries(jsImports(text).map((i) => [i.spec, i.how]));
  assert.deepEqual(got, { 'node:fs': 'static', './a.js': 'static', './side.js': 'static', '../c.js': 'reexport', './star.js': 'reexport', './lazy.js': 'dynamic', pkg: 'require', 'node:path': 'builtin' });
});

test('JavaScript files resolve relative imports to files, with and without the extension, and mark externals', () => {
  const dir = repoWith({
    'src/a.js': "import './b.js'; import './dir'; import './missing.js'; import x from 'left-pad'; await import('./b.js');",
    'src/b.js': 'export {};',
    'src/dir/index.js': 'export {};',
  });
  const f = extractFile(dir, 'src/a.js');
  const by = Object.fromEntries(f.imports.map((i) => [i.spec, i]));
  assert.equal(by['./b.js'].resolved, 'src/b.js');
  assert.equal(by['./b.js'].how, 'static', 'a specifier reached statically and dynamically is a static import');
  assert.equal(by['./dir'].resolved, 'src/dir/index.js');
  assert.deepEqual([by['./missing.js'].resolved, by['./missing.js'].external], [null, false]);
  assert.deepEqual([by['left-pad'].resolved, by['left-pad'].external], [null, true]);
  const lazy = extractFile(repoWith({ 'src/a.js': "const m = await import('./b.js');", 'src/b.js': '' }), 'src/a.js');
  assert.equal(lazy.imports[0].how, 'dynamic');
});

test('Lean: import lines resolve to files under formal/, other imports are external, comments ignored', () => {
  const dir = repoWith({
    'formal/Exegra.lean': 'import Exegra.Json\nimport Lean\n-- import Exegra.Commented\n/- import Exegra.Block -/\nimport Exegra.Core.LTS\n',
    'formal/Exegra/Json.lean': 'import Lean\n',
    'formal/Exegra/Core/LTS.lean': '',
  });
  const f = extractFile(dir, 'formal/Exegra.lean');
  assert.deepEqual(f.imports.map((i) => [i.spec, i.resolved, i.external]), [['Exegra.Json', 'formal/Exegra/Json.lean', false], ['Lean', null, true], ['Exegra.Core.LTS', 'formal/Exegra/Core/LTS.lean', false]]);
});

test('Rust: mod declarations and crate-relative use paths resolve to module files', () => {
  const dir = repoWith({
    'engine/core/Cargo.toml': '[package]\nname = "my-core"\n',
    'engine/core/src/lib.rs': 'pub mod value;\nmod engine;\nuse std::fmt;\n',
    'engine/core/src/value.rs': 'pub struct V;\n',
    'engine/core/src/engine.rs': 'use crate::value::V;\nuse crate::{value::V as W};\nuse super::value;\n',
    'engine/wasm/Cargo.toml': '[package]\nname = "my-wasm"\n',
    'engine/wasm/src/lib.rs': 'use my_core::engine::run;\n',
  });
  const lib = extractFile(dir, 'engine/core/src/lib.rs');
  assert.deepEqual(lib.imports.filter((i) => i.how === 'mod').map((i) => [i.spec, i.resolved]), [['value', 'engine/core/src/value.rs'], ['engine', 'engine/core/src/engine.rs']]);
  assert.equal(lib.imports.find((i) => i.spec === 'std::fmt')?.external, true);
  const eng = extractFile(dir, 'engine/core/src/engine.rs');
  assert.ok(eng.imports.filter((i) => i.spec.startsWith('crate::')).every((i) => i.resolved === 'engine/core/src/value.rs'));
  const wasm = extractFile(dir, 'engine/wasm/src/lib.rs');
  assert.equal(wasm.imports[0].resolved, 'engine/core/src/engine.rs');
});

test('a fact is a function of the file bytes: unchanged files give unchanged facts, a touched file changes only its own', () => {
  const dir = repoWith({ 'src/a.js': "import './b.js';", 'src/b.js': "import './c.js';", 'src/c.js': 'export {};', 'formal/X.lean': 'import Lean\n' });
  const one = extractRepository(dir);
  assert.deepEqual(extractRepository(dir), one, 'extracting twice gives the same facts');
  assert.deepEqual(checkFacts(one), []);
  assert.equal(one.extractor.version, EXTRACTOR.version);
  // Touch one file: new bytes with the same imports, then new imports.
  fs.appendFileSync(path.join(dir, 'src/b.js'), '\n// touched\n');
  const two = extractRepository(dir);
  const changed = two.files.filter((f, i) => JSON.stringify(f) !== JSON.stringify(one.files[i])).map((f) => f.path);
  assert.deepEqual(changed, ['src/b.js']);
  assert.deepEqual(two.files.find((f) => f.path === 'src/b.js')?.imports, one.files.find((f) => f.path === 'src/b.js')?.imports, 'a comment changes the digest, not the imports');
  assert.deepEqual(factsDrift(one, dir).changed, ['src/b.js']);
  fs.writeFileSync(path.join(dir, 'src/c.js'), "import './a.js';");
  const three = extractRepository(dir);
  assert.deepEqual(three.files.filter((f, i) => JSON.stringify(f) !== JSON.stringify(two.files[i])).map((f) => f.path), ['src/c.js']);
  // A new file and a removed file are drift too.
  fs.writeFileSync(path.join(dir, 'src/d.js'), '');
  fs.rmSync(path.join(dir, 'src/a.js'));
  const drift = factsDrift(three, dir);
  assert.deepEqual([drift.missing, drift.gone], [['src/d.js'], ['src/a.js']]);
});

test('the digest does not depend on the newline convention of the checkout', () => {
  assert.equal(digestOf('a\r\nb\r\n'), digestOf('a\nb\n'));
  assert.notEqual(digestOf('a\nb\n'), digestOf('a\nc\n'));
});

test('the committed fact file of this repository describes the tree', () => {
  const stored = readFacts(path.join(ROOT, FACTS_PATH));
  assert.ok(stored, `${FACTS_PATH} exists; write it with node tools/extract.js`);
  assert.deepEqual(checkFacts(stored), []);
  const drift = factsDrift(stored, ROOT);
  assert.deepEqual(drift, { changed: [], missing: [], gone: [], extractor: false, evidence: false }, 'run node tools/extract.js (or exegra extract) and commit the fact file');
  // Every extracted file is a file of the surface, with a resolved import for every relative specifier that exists.
  for (const f of stored.files) for (const i of f.imports) if (i.resolved !== null) assert.ok(fs.existsSync(path.join(ROOT, i.resolved)), `${f.path} imports ${i.spec}, which resolves to ${i.resolved}`);
});
