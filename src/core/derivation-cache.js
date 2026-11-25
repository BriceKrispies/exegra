// A persistent cache of the derived model (WG-5636): the stages of derivation that run in the Lean
// kernel, whose results are plain data, are stored on disk and reused by later processes.
//
// parseSpec stores the model it derives from a specification text, analyzeSpec the semantic
// diagnostics validation finds in it. Both are pure functions of the text and of Exegra's own
// derivation sources, so a hit is observably identical to a miss: the same values, rebuilt with the
// same shapes (Maps, null-prototype objects, shared references, -0 and the rest; see encode below).
//
// The key (derivationKey) is the SHA-256 of: the entry format, the package version, the content hash of
// Exegra's derivation sources (every file of src/core and of the Lean build in src/engine/lean), the
// stage name and the stage's inputs (the specification text, which for a layered project already holds
// every product file's entities, and the options that change the result). No modification time is
// read. Files under the project's specs directory and project.jsonc reach the key through what they
// name: the text of each file read.
//
// Storage: one file per entry, `<stage>-<key>.entry`, in cacheDirectory(): EXEGRA_MODEL_CACHE_DIR, else
// `model/` under EXEGRA_CACHE_DIR (the tool cache of tools/build-formal-wasm.js), else `exegra/cache/model`
// under %LOCALAPPDATA% (Windows) or $XDG_CACHE_HOME / ~/.cache. EXEGRA_NO_CACHE=1 disables it.
// A write goes to a temporary sibling and is renamed into place, so a reader sees a whole entry or none;
// an entry that is truncated, altered or from another format is a miss, never an error. Past
// EXEGRA_MODEL_CACHE_MAX_BYTES (default 512 MiB) the least recently used entries are deleted.
//
// The module is importable by the browser bundle: it reaches node:fs and friends only through
// process.getBuiltinModule and does nothing when they are absent.

const FORMAT = 1;
const DEFAULT_MAX_BYTES = 512 * 1024 * 1024;
const STALE_TEMP_MS = 60 * 60 * 1000;

const nodeProcess = typeof process !== 'undefined' && typeof process?.getBuiltinModule === 'function' ? process : null;

/** What this process did, by stage, for tests and EXEGRA_CACHE_TRACE=1. @type {Record<string, {hit: number, miss: number, store: number}>} */
export const cacheStats = {};

/** @param {string} stage @param {'hit'|'miss'|'store'} what */
function note(stage, what) {
  (cacheStats[stage] ??= { hit: 0, miss: 0, store: 0 })[what]++;
  if (nodeProcess?.env.EXEGRA_CACHE_TRACE) nodeProcess.stderr.write(`exegra-cache: ${what} ${stage}\n`);
}

/** @returns {{fs: typeof import('node:fs'), path: typeof import('node:path'), crypto: typeof import('node:crypto'), os: typeof import('node:os')}|null} */
function node() {
  if (!nodeProcess) return null;
  const get = (/** @type {string} */ n) => /** @type {any} */ (nodeProcess.getBuiltinModule(n));
  return { fs: get('node:fs'), path: get('node:path'), crypto: get('node:crypto'), os: get('node:os') };
}

/** Whether the cache is switched off (EXEGRA_NO_CACHE set to anything but empty, 0 or false). */
export function cacheDisabled() {
  const v = nodeProcess?.env.EXEGRA_NO_CACHE;
  return v !== undefined && v !== '' && v !== '0' && v.toLowerCase() !== 'false';
}

/** The directory entries are kept in. @returns {string|null} */
export function cacheDirectory() {
  const n = node();
  if (!n || !nodeProcess) return null;
  const env = nodeProcess.env;
  if (env.EXEGRA_MODEL_CACHE_DIR) return n.path.resolve(env.EXEGRA_MODEL_CACHE_DIR);
  if (env.EXEGRA_CACHE_DIR) return n.path.join(n.path.resolve(env.EXEGRA_CACHE_DIR), 'model');
  if (nodeProcess.platform === 'win32' && env.LOCALAPPDATA) return n.path.join(env.LOCALAPPDATA, 'exegra', 'cache', 'model');
  return n.path.join(env.XDG_CACHE_HOME || n.path.join(n.os.homedir(), '.cache'), 'exegra', 'model');
}

// ---------------------------------------------------------------------------------------------
// The key

/** @type {Map<string, string>} */
const sourceHashes = new Map();

/**
 * The content hash of Exegra's derivation sources: the package version, then every file under
 * src/core and src/engine/lean (path and bytes), in path order.
 * @param {string} [root] the Exegra checkout (default: the one this module is in)
 * @returns {string|null}
 */
export function derivationSourceHash(root) {
  const n = node();
  if (!n) return null;
  const { fs, path, crypto } = n;
  const base = root ?? path.resolve(path.dirname(/** @type {any} */ (nodeProcess).getBuiltinModule('node:url').fileURLToPath(import.meta.url)), '..', '..');
  const known = root === undefined ? sourceHashes.get(base) : undefined;
  if (known) return known;
  const h = crypto.createHash('sha256');
  try {
    h.update(`package ${JSON.parse(fs.readFileSync(path.join(base, 'package.json'), 'utf8')).version}\n`);
    /** @param {string} dir @returns {string[]} */
    const walk = (dir) => fs.readdirSync(dir, { withFileTypes: true })
      .flatMap((e) => (e.isDirectory() ? walk(path.join(dir, e.name)) : [path.join(dir, e.name)]));
    const files = ['src/core', 'src/engine/lean'].flatMap((d) => walk(path.join(base, d)))
      .map((f) => path.relative(base, f).split(path.sep).join('/')).sort();
    for (const f of files) {
      const bytes = fs.readFileSync(path.join(base, f));
      h.update(`${f} ${bytes.length}\n`);
      h.update(bytes);
    }
  } catch {
    return null; // the sources cannot be read (an unbuilt Lean core, say): no cache
  }
  const out = h.digest('hex');
  if (root === undefined) sourceHashes.set(base, out);
  return out;
}

/**
 * The key of one stage's result.
 * @param {string} stage @param {unknown} inputs everything the stage's result depends on, besides the sources
 * @param {string} [root]
 * @returns {string|null}
 */
export function derivationKey(stage, inputs, root) {
  const n = node();
  const sources = derivationSourceHash(root);
  if (!n || !sources) return null;
  return n.crypto.createHash('sha256').update(JSON.stringify([FORMAT, stage, sources, inputs])).digest('hex');
}

// ---------------------------------------------------------------------------------------------
// A faithful encoding of the plain data a stage returns
//
// Every composite is a tagged JSON array, so no data can be mistaken for a tag:
//   ["a", ...items]                       array
//   ["o", 0|1, key, value, ...]           object with Object.prototype (0) or none (1)
//   ["m", key, value, ...]  ["s", ...]    Map, Set
//   ["d", id, composite]  ["r", id]       a composite reached again, first time and later (sharing, cycles)
//   ["u"]  ["n", "-0"|"NaN"|...]          undefined, the numbers JSON cannot write
// Anything else (functions, symbols, bigints, class instances, holes, accessors) cannot be reproduced
// exactly, so the encoding refuses it and the stage is simply not cached.

/** @param {unknown} root @returns {string} JSON text */
export function encode(root) {
  /** @type {Map<object, number>} */
  const seen = new Map();
  /** @param {any} v */
  const count = (v) => {
    if (typeof v !== 'object' || v === null) return;
    const c = seen.get(v);
    if (c !== undefined) { seen.set(v, c + 1); return; }
    seen.set(v, 1);
    if (Array.isArray(v)) { for (let i = 0; i < v.length; i++) count(v[i]); }
    else if (v instanceof Map) { for (const [k, x] of v) { count(k); count(x); } }
    else if (v instanceof Set) { for (const x of v) count(x); }
    else for (const k of Object.keys(v)) count(v[k]);
  };
  count(root);
  /** @type {Map<object, number>} */
  const ids = new Map();
  /** @param {any} v @returns {any} */
  const emit = (v) => {
    switch (typeof v) {
      case 'string': case 'boolean': return v;
      case 'undefined': return ['u'];
      case 'number':
        if (Object.is(v, -0)) return ['n', '-0'];
        return Number.isFinite(v) ? v : ['n', String(v)];
      case 'object': break;
      default: throw new Error(`cannot encode a ${typeof v}`);
    }
    if (v === null) return null;
    const id = ids.get(v);
    if (id !== undefined) return ['r', id];
    const shared = /** @type {number} */ (seen.get(v)) > 1;
    if (shared) ids.set(v, ids.size);
    const sharedId = shared ? ids.get(v) : -1;
    const proto = Object.getPrototypeOf(v);
    /** @type {any[]} */
    let out;
    if (Array.isArray(v)) {
      out = ['a'];
      for (let i = 0; i < v.length; i++) {
        if (!(i in v)) throw new Error('cannot encode an array with holes');
        out.push(emit(v[i]));
      }
    } else if (v instanceof Map && proto === Map.prototype) {
      out = ['m'];
      for (const [k, x] of v) out.push(emit(k), emit(x));
    } else if (v instanceof Set && proto === Set.prototype) {
      out = ['s'];
      for (const x of v) out.push(emit(x));
    } else if (proto === Object.prototype || proto === null) {
      out = ['o', proto === null ? 1 : 0];
      for (const k of Object.keys(v)) {
        const d = /** @type {PropertyDescriptor} */ (Object.getOwnPropertyDescriptor(v, k));
        if (!('value' in d)) throw new Error('cannot encode an accessor');
        out.push(k, emit(v[k]));
      }
    } else {
      throw new Error('cannot encode an instance of a class');
    }
    return shared ? ['d', sharedId, out] : out;
  };
  return JSON.stringify(emit(root));
}

/** @param {string} text JSON text from encode @returns {any} */
export function decode(text) {
  /** @type {any[]} */
  const defined = [];
  /** @param {any} t @param {number} [id] @returns {any} */
  const build = (t, id) => {
    if (!Array.isArray(t)) return t;
    switch (t[0]) {
      case 'u': return undefined;
      case 'n': return t[1] === '-0' ? -0 : Number(t[1]);
      case 'r': {
        if (!(t[1] in defined)) throw new Error('bad reference');
        return defined[t[1]];
      }
      case 'd': return build(t[2], t[1]);
      case 'a': {
        /** @type {any[]} */
        const a = new Array(t.length - 1);
        if (id !== undefined) defined[id] = a;
        for (let i = 1; i < t.length; i++) a[i - 1] = build(t[i]);
        return a;
      }
      case 'm': {
        const m = new Map();
        if (id !== undefined) defined[id] = m;
        for (let i = 1; i < t.length; i += 2) m.set(build(t[i]), build(t[i + 1]));
        return m;
      }
      case 's': {
        const s = new Set();
        if (id !== undefined) defined[id] = s;
        for (let i = 1; i < t.length; i++) s.add(build(t[i]));
        return s;
      }
      case 'o': {
        /** @type {any} */
        const o = t[1] === 1 ? Object.create(null) : {};
        if (id !== undefined) defined[id] = o;
        for (let i = 2; i < t.length; i += 2) {
          const k = t[i];
          if (k === '__proto__') Object.defineProperty(o, k, { value: build(t[i + 1]), enumerable: true, writable: true, configurable: true });
          else o[k] = build(t[i + 1]);
        }
        return o;
      }
      default: throw new Error('bad tag');
    }
  };
  return build(JSON.parse(text));
}

// ---------------------------------------------------------------------------------------------
// Entries

/**
 * Read an entry; any problem is a miss.
 * @param {string} file @param {string} key @returns {{value: any}|null}
 */
function readEntry(file, key) {
  const n = /** @type {NonNullable<ReturnType<typeof node>>} */ (node());
  try {
    const buf = n.fs.readFileSync(file);
    const cut = buf.indexOf(10);
    if (cut < 0) return null;
    const head = JSON.parse(buf.subarray(0, cut).toString('utf8'));
    const body = buf.subarray(cut + 1);
    if (head.format !== FORMAT || head.key !== key || head.bytes !== body.length) return null;
    if (n.crypto.createHash('sha256').update(body).digest('hex') !== head.sha256) return null;
    const value = decode(body.toString('utf8'));
    try { const now = new Date(); n.fs.utimesSync(file, now, now); } catch { /* recency only */ }
    return { value };
  } catch {
    return null;
  }
}

/** Write an entry through a temporary sibling and a rename. @param {string} dir @param {string} file @param {string} key @param {string} body */
function writeEntry(dir, file, key, body) {
  const n = /** @type {NonNullable<ReturnType<typeof node>>} */ (node());
  const bytes = Buffer.from(body, 'utf8');
  const head = JSON.stringify({ format: FORMAT, key, bytes: bytes.length, sha256: n.crypto.createHash('sha256').update(bytes).digest('hex') });
  const tmp = `${file}.${nodeProcess?.pid}.${n.crypto.randomBytes(6).toString('hex')}.tmp`;
  try {
    n.fs.mkdirSync(dir, { recursive: true });
    n.fs.writeFileSync(tmp, Buffer.concat([Buffer.from(`${head}\n`), bytes]));
    n.fs.renameSync(tmp, file);
  } catch {
    try { n.fs.rmSync(tmp, { force: true }); } catch { /* nothing to clean */ }
    return false;
  }
  return true;
}

/** Delete the least recently used entries beyond the size bound, and temporary files left by a dead writer. @param {string} dir */
function evict(dir) {
  const n = /** @type {NonNullable<ReturnType<typeof node>>} */ (node());
  const max = Number(nodeProcess?.env.EXEGRA_MODEL_CACHE_MAX_BYTES) > 0 ? Number(nodeProcess?.env.EXEGRA_MODEL_CACHE_MAX_BYTES) : DEFAULT_MAX_BYTES;
  try {
    const now = Date.now();
    /** @type {{file: string, size: number, time: number}[]} */
    const entries = [];
    let total = 0;
    for (const name of n.fs.readdirSync(dir)) {
      const file = n.path.join(dir, name);
      let st;
      try { st = n.fs.statSync(file); } catch { continue; }
      if (name.endsWith('.tmp')) {
        if (now - st.mtimeMs > STALE_TEMP_MS) n.fs.rmSync(file, { force: true });
        continue;
      }
      if (!name.endsWith('.entry')) continue;
      entries.push({ file, size: st.size, time: st.mtimeMs });
      total += st.size;
    }
    if (total <= max) return;
    entries.sort((a, b) => a.time - b.time);
    const target = max * 0.75;
    for (const e of entries) {
      if (total <= target) break;
      try { n.fs.rmSync(e.file, { force: true }); total -= e.size; } catch { /* in use elsewhere */ }
    }
  } catch { /* eviction is best effort */ }
}

/**
 * The result of `compute()`, from the cache when the same stage over the same inputs was computed
 * before by Exegra's present sources, else computed (and stored). `compute` must be a pure function of
 * `inputs` and the sources; a result the encoding cannot reproduce exactly, or one `worth` rejects, is
 * returned without being stored.
 * @template T
 * @param {string} stage @param {unknown} inputs @param {() => T} compute @param {(value: T) => boolean} [worth]
 * @returns {T}
 */
export function cachedStage(stage, inputs, compute, worth) {
  if (cacheDisabled()) return compute();
  const dir = cacheDirectory();
  const key = dir ? derivationKey(stage, inputs) : null;
  if (!dir || !key) return compute();
  const n = /** @type {NonNullable<ReturnType<typeof node>>} */ (node());
  const file = n.path.join(dir, `${stage}-${key}.entry`);
  const hit = readEntry(file, key);
  if (hit) { note(stage, 'hit'); return hit.value; }
  note(stage, 'miss');
  const value = compute();
  if (worth && !worth(value)) return value;
  let body;
  try { body = encode(value); } catch { return value; }
  if (writeEntry(dir, file, key, body)) { note(stage, 'store'); evict(dir); }
  return value;
}
