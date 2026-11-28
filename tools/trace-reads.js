// A preload (`node --import`) that records which repository files and directories a test process loaded or read, for
// change impact and for reusing a recorded pass (cli/test-batch.js): the modules it loaded (the scripts it executed)
// and the data it read through `fs` (fixtures, the specification, the WebAssembly builds). Each process (the test runner, its test files, the processes they spawn, worker
// threads) writes `reads-<pid>-<thread>.json` into the directory named by EXEGRA_TRACE_DIR when it exits.
// Only reads under EXEGRA_TRACE_ROOT are kept; node_modules is left out. Paths are repository-relative with
// forward slashes; a directory read lists its name with a trailing slash.

import childProcess from 'node:child_process';
import fs from 'node:fs';
import { registerHooks, syncBuiltinESMExports } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { threadId } from 'node:worker_threads';

const dir = process.env.EXEGRA_TRACE_DIR;
const root = process.env.EXEGRA_TRACE_ROOT;
if (dir && root) {
  const base = path.resolve(root);
  const files = new Set();
  const dirs = new Set();
  /** @param {any} p @param {Set<string>} into */
  const note = (p, into) => {
    try {
      let abs;
      if (typeof p === 'string') abs = path.resolve(p);
      else if (p instanceof URL) abs = fileURLToPath(p);
      else if (Buffer.isBuffer(p)) abs = path.resolve(p.toString());
      else return;
      const rel = path.relative(base, abs);
      if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) return;
      const parts = rel.split(path.sep);
      if (parts.includes('node_modules') || parts[0] === '.git' || parts[0] === '.outcomes') return;
      into.add(parts.join('/'));
    } catch { /* an unusable path is not recorded */ }
  };
  /** @param {any} target @param {string} name @param {Set<string>} into */
  const wrap = (target, name, into) => {
    const original = target[name];
    if (typeof original !== 'function') return;
    target[name] = function (/** @type {any[]} */ ...args) {
      note(args[0], into);
      return original.apply(this, args);
    };
  };
  for (const n of ['readFileSync', 'readFile', 'createReadStream']) wrap(fs, n, files);
  wrap(fs.promises, 'readFile', files);
  // A probe for a file decides whether a test skips (a binary that is not built), so it counts as a read.
  for (const n of ['existsSync', 'statSync']) wrap(fs, n, files);
  for (const n of ['readdirSync', 'readdir']) wrap(fs, n, dirs);
  wrap(fs.promises, 'readdir', dirs);
  // Programs other than node and git that a process starts: what they read is not seen here.
  const tools = new Set();
  const SELF = new Set(['node', 'git', path.basename(process.execPath, path.extname(process.execPath)).toLowerCase()]);
  for (const n of ['spawn', 'spawnSync', 'execFile', 'execFileSync', 'exec', 'execSync', 'fork']) {
    const original = /** @type {any} */ (childProcess)[n];
    if (typeof original !== 'function') continue;
    /** @param {any[]} args */
    const note = (args) => {
      try {
        let cmd = typeof args[0] === 'string' ? args[0] : '';
        if (n === 'exec' || n === 'execSync') cmd = cmd.trim().split(/s+/)[0] ?? '';
        const name = n === 'fork' ? 'node' : path.basename(cmd.replace(/^"|"$/g, ''), path.extname(cmd)).toLowerCase();
        if (name && !SELF.has(name)) tools.add(name);
      } catch { /* not recorded */ }
    };
    const wrapper = /** @type {any} */ (/** @this {any} @param {any[]} args */ function (...args) {
      note(args);
      return original.apply(this, args);
    });
    const own = /** @type {any} */ (Object.getOwnPropertyDescriptors(original));
    delete own.prototype; // a function expression's own prototype cannot be redefined
    delete own[promisify.custom];
    Object.defineProperties(wrapper, own);
    // util.promisify reads a promisified form from a symbol property of the function.
    const custom = original[promisify.custom];
    if (typeof custom === 'function') Object.defineProperty(wrapper, promisify.custom, { value: function (/** @type {any[]} */ ...args) { note(args); return custom.apply(this, args); }, configurable: true });
    /** @type {any} */ (childProcess)[n] = wrapper;
  }
  // Every script and data module that is loaded (ESM, CommonJS, JSON): the files a run executed. This stands in for V8
  // coverage, which names the same scripts (a loaded script has run its top level) at a multiple of the run time.
  registerHooks({
    load(url, context, nextLoad) {
      if (url.startsWith('file:')) note(new URL(url), files);
      return nextLoad(url, context);
    },
  });
  syncBuiltinESMExports();
  process.on('exit', () => {
    try {
      fs.writeFileSync(path.join(dir, `reads-${process.pid}-${threadId}.json`), JSON.stringify({ files: [...files], dirs: [...dirs], tools: [...tools] }));
    } catch { /* the trace is best effort; a run without one has no recorded reads */ }
  });
}
