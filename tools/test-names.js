// A static scan of the test names a test file declares, for `exegra validate`: an evidence reference
// `file#name` whose name matches no test the file declares can never pass, and validate says so before verify runs.
//
// The scan reads `test(...)`, `it(...)`, `describe(...)` and `suite(...)` calls (with their `.skip`, `.only`,
// `.todo`, `.describe`, ... forms) whose first argument is a string literal. A name built at run time (a template with
// `${}`, a variable) cannot be known, so a file with any such call is `dynamic` and its references are not refused.

import fs from 'node:fs';
import path from 'node:path';
import { compilePattern, splitRef } from '../cli/outcomes.js';

const CALL = /(?<![.\w$])(test|it|describe|suite)((?:\.\w+)*)\s*\(\s*/g;

/**
 * The names a source declares.
 * @param {string} source
 * @returns {{tests: string[], suites: string[], dynamic: boolean}}
 */
export function declaredTestNames(source) {
  /** @type {string[]} */
  const tests = [];
  /** @type {string[]} */
  const suites = [];
  let dynamic = false;
  for (const m of source.matchAll(CALL)) {
    const at = m.index + m[0].length;
    const q = source[at];
    // `test.skip()` and friends with no title, and a callback as the first argument, declare no name.
    if (q === undefined || /[)\]}]/.test(q) || source.startsWith('async', at) || source.startsWith('function', at) || q === '(' || q === '{') continue;
    const isSuite = m[1] === 'describe' || m[1] === 'suite' || m[2].split('.').includes('describe');
    if (q !== '"' && q !== "'" && q !== '`') {
      // An identifier is a name known only at run time; a modifier call such as test.skip(cond) is not a declaration.
      if (/[A-Za-z_$]/.test(q) && !/^\.(skip|fixme|slow|fail|setTimeout|use|info|step|beforeEach|afterEach|beforeAll|afterAll|expect)\b/.test(m[2])) dynamic = true;
      continue;
    }
    let i = at + 1;
    let text = '';
    let interpolated = false;
    while (i < source.length && source[i] !== q) {
      if (source[i] === '\\') { text += source[i + 1] ?? ''; i += 2; continue; }
      if (q === '`' && source[i] === '$' && source[i + 1] === '{') interpolated = true;
      text += source[i];
      i++;
    }
    // A string followed by `+` or another operator is built at run time.
    const after = /^\s*(.)/.exec(source.slice(i + 1))?.[1];
    if (interpolated || (after !== ',' && after !== ')')) { dynamic = true; continue; }
    // `test.skip('title', ...)` is a declaration; `test.skip(true, 'reason')` is not (its first argument is no string).
    (isSuite ? suites : tests).push(text);
  }
  return { tests, suites, dynamic };
}

/**
 * Whether a reference's name pattern can match a test of the file, and why not. True when the file declares a test
 * (or suite) the pattern matches, alone or with a suite name in front, or when the file names tests at run time.
 * @param {string} ref @param {string} source the test file's text
 * @returns {boolean}
 */
export function refNamesATest(ref, source) {
  const { file, pattern } = splitRef(ref);
  if (!pattern) return true;
  const browser = file.startsWith('tests/browser/');
  const re = compilePattern(pattern, browser ? 'i' : '');
  if (!re) return true; // not an expression: verify reports it
  const names = declaredTestNames(source);
  if (names.dynamic) return true;
  const all = [...names.tests, ...names.suites];
  const prefixed = names.suites.flatMap((s) => names.tests.map((t) => `${s} ${t}`));
  const fileTitled = browser ? [...all, ...prefixed].map((n) => `${file} ${n}`) : [];
  return [...all, ...prefixed, ...fileTitled].some((n) => re.test(n));
}

/**
 * Diagnostics for the test evidence of a model whose reference names no test its file declares.
 * @param {{byKind: Record<string, any[]>}} model @param {string} repoRoot
 * @returns {{code: string, severity: 'error', message: string, entityId: string, path: (string|number)[]}[]}
 */
export function evidenceRefDiagnostics(model, repoRoot) {
  /** @type {Map<string, string|null>} */
  const sources = new Map();
  const out = [];
  for (const e of model.byKind.evidence ?? []) {
    if (e.data.kind !== 'test' || typeof e.data.ref !== 'string') continue;
    const ref = e.data.ref;
    const { file } = splitRef(ref);
    if (!file || /^[a-z][a-z0-9_-]*:/.test(file) || file.includes('..')) continue;
    if (!sources.has(file)) {
      /** @type {string|null} */
      let text = null;
      try { text = fs.readFileSync(path.resolve(repoRoot, file), 'utf8'); } catch { /* a missing file is verify's finding */ }
      sources.set(file, text);
    }
    const source = sources.get(file);
    if (source === null || source === undefined) continue;
    if (!refNamesATest(ref, source)) {
      out.push({
        code: 'evidence.ref-no-test', severity: /** @type {const} */ ('error'), entityId: e.id, path: ['ref'],
        message: `Evidence "${e.id}": the reference "${ref}" names no test that ${file} declares, so it can never pass.`,
      });
    }
  }
  return out;
}
