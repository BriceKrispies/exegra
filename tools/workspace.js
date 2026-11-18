// Node-only filesystem boundary for Exegra projects. Everything that touches
// specs/<name>/ goes through here. Not part of src/core, so it may use node:*.
//
// A project's specification is specs/<name>/spec.jsonc, unless the project
// directory holds project.jsonc naming another file: {"spec": "<relative path>"}.
// That lets a project's specification live in the repository it describes while
// its presentation (layout), recorded results, journal and generated artifacts
// stay here. project.jsonc may also declare realisation roots ({"roots": {...}},
// see tools/realisation-roots.js). It is never written through this module.

import { createHash } from 'node:crypto';
import { promises as fs, readFileSync, watch as fsWatch } from 'node:fs';
import path from 'node:path';
import { parse as parseJsonc } from 'jsonc-parser';

/** Logical file key -> path relative to a project directory (forward slashes). */
export const WORKSPACE_FILES = {
  spec: 'spec.jsonc',
  layout: 'layout.jsonc',
  recorded: 'evidence/results.json',
};

const BUNDLE_FORMAT = 'exegra-project';
const BUNDLE_VERSION = 1;
const BUNDLE_KEYS = new Set(Object.values(WORKSPACE_FILES));
const JOURNAL_REL = '.history/journal.jsonl';
/** The file that may point a project at a specification stored elsewhere. */
export const PROJECT_FILE = 'project.jsonc';
const NAME_RE = /^[a-z0-9][a-z0-9_-]{0,63}$/;
const MAX_TEXT_BYTES = 16 * 1024 * 1024;
const RENAME_RETRIES = 5;
const RENAME_DELAY_MS = 20;
const DEBOUNCE_MS = 80;

/** Error with a stable machine-readable `code`. */
export class WorkspaceError extends Error {
  /**
   * @param {string} code  'name.invalid' | 'path.unsafe' | 'file.unknown' | 'not-found' | 'bundle.invalid' | 'too-large' | 'input.invalid' | 'project.invalid'
   * @param {string} message
   */
  constructor(code, message) {
    super(message);
    this.name = 'WorkspaceError';
    this.code = code;
  }
}

/**
 * sha256 hex of the UTF-8 text.
 * @param {string} text
 * @returns {string}
 */
export function hashText(text) {
  return createHash('sha256').update(text, 'utf8').digest('hex');
}

/** @param {unknown} name @returns {asserts name is string} */
function assertName(name) {
  if (typeof name !== 'string' || !NAME_RE.test(name)) {
    throw new WorkspaceError('name.invalid', `Invalid project name: ${JSON.stringify(name)}.`);
  }
}

/** @param {string} text @param {string} [what] */
function assertText(text, what = 'text') {
  if (typeof text !== 'string') {
    throw new WorkspaceError('input.invalid', `${what} must be a string.`);
  }
  if (Buffer.byteLength(text, 'utf8') > MAX_TEXT_BYTES) {
    throw new WorkspaceError('too-large', `${what} is larger than 16 MB.`);
  }
}

/** @param {unknown} value @returns {value is Record<string, any>} */
function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

/** True when target is strictly inside base (both absolute). */
function isInside(base, target) {
  const rel = path.relative(base, target);
  return (
    rel !== '' &&
    !path.isAbsolute(rel) &&
    rel !== '..' &&
    !rel.startsWith(`..${path.sep}`)
  );
}

/** @param {string} file @returns {Promise<string|null>} null when missing */
async function readOptional(file) {
  try {
    return await fs.readFile(file, 'utf8');
  } catch (err) {
    if (/** @type {NodeJS.ErrnoException} */ (err).code === 'ENOENT' || /** @type {NodeJS.ErrnoException} */ (err).code === 'ENOTDIR') return null;
    throw err;
  }
}

/** Synchronous variant used when seeding watch state. */
function hashOfFileSync(file) {
  try {
    return hashText(readFileSync(file, 'utf8'));
  } catch {
    return null;
  }
}

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
let tmpCounter = 0;

/**
 * Atomic replace: write a sibling tmp file, then rename over the target.
 * Windows can hold the target briefly (EPERM/EBUSY); retry, then write in place.
 * @param {string} target
 * @param {string} text
 */
async function atomicWrite(target, text) {
  await fs.mkdir(path.dirname(target), { recursive: true });
  const tmp = `${target}.${process.pid}.${++tmpCounter}.tmp`;
  try {
    await fs.writeFile(tmp, text, 'utf8');
    for (let attempt = 0; attempt <= RENAME_RETRIES; attempt++) {
      if (attempt > 0) await sleep(RENAME_DELAY_MS);
      try {
        await fs.rename(tmp, target);
        return;
      } catch (err) {
        if (/** @type {NodeJS.ErrnoException} */ (err).code !== 'EPERM' && /** @type {NodeJS.ErrnoException} */ (err).code !== 'EBUSY') throw err;
      }
    }
    await fs.writeFile(target, text, 'utf8');
  } finally {
    await fs.rm(tmp, { force: true }).catch(() => {});
  }
}

/** Serialises operations per project so the read-check-write and journal stay ordered. */
const locks = new Map();

/**
 * @template T
 * @param {string} key
 * @param {() => Promise<T>} fn
 * @returns {Promise<T>}
 */
function withProjectLock(key, fn) {
  const prev = locks.get(key) ?? Promise.resolve();
  const run = prev.then(fn);
  const tail = run.then(() => {}, () => {});
  locks.set(key, tail);
  tail.then(() => {
    if (locks.get(key) === tail) locks.delete(key);
  });
  return run;
}

/** @param {string|null} text */
function parseRecorded(text) {
  if (text === null) return null;
  try {
    return JSON.parse(text);
  } catch {
    return null;
  }
}

/** @param {string} text @param {string} fallback */
function titleOf(text, fallback) {
  try {
    const data = parseJsonc(text);
    const name = data?.system?.name;
    return typeof name === 'string' && name.trim() !== '' ? name : fallback;
  } catch {
    return fallback;
  }
}

/**
 * Validates an import bundle and returns its file texts.
 * @param {unknown} bundle
 * @returns {Record<string, string>}
 */
function validateBundle(bundle) {
  /** @type {(message: string) => never} */
  const fail = (message) => {
    throw new WorkspaceError('bundle.invalid', message);
  };
  if (!isPlainObject(bundle)) fail('Bundle must be an object.');
  if (bundle.format !== BUNDLE_FORMAT) fail(`Bundle format must be "${BUNDLE_FORMAT}".`);
  if (bundle.version !== BUNDLE_VERSION) {
    fail(`Unsupported bundle version ${JSON.stringify(bundle.version)}.`);
  }
  if (!isPlainObject(bundle.files)) fail('Bundle files must be an object.');
  const files = bundle.files;
  for (const key of Object.keys(files)) {
    if (!BUNDLE_KEYS.has(key)) fail(`Bundle contains unknown file "${key}".`);
  }
  if (typeof files[WORKSPACE_FILES.spec] !== 'string') {
    fail(`Bundle must include ${WORKSPACE_FILES.spec} as a string.`);
  }
  const out = {};
  for (const key of Object.keys(files)) {
    const text = files[key];
    if (typeof text !== 'string') fail(`Bundle file "${key}" must be a string.`);
    assertText(text, key);
    out[key] = text;
  }
  return out;
}

/**
 * @param {string} rootDir absolute path of the `specs` directory
 */
export function createWorkspace(rootDir) {
  const root = path.resolve(rootDir);

  /** @param {string} name */
  const projectKey = (name) => {
    assertName(name);
    return path.join(root, name);
  };

  /**
   * Safe absolute path for relPath inside project `name`, or throws.
   * @param {string} name
   * @param {string} relPath
   * @returns {string}
   */
  function resolve(name, relPath) {
    assertName(name);
    if (typeof relPath !== 'string' || relPath === '') {
      throw new WorkspaceError('input.invalid', 'Path must be a non-empty string.');
    }
    if (path.isAbsolute(relPath)) {
      throw new WorkspaceError('path.unsafe', `Absolute path not allowed: ${relPath}`);
    }
    const projectDir = path.resolve(root, name);
    const target = path.resolve(path.join(root, name, relPath));
    if (!isInside(projectDir, target)) {
      throw new WorkspaceError('path.unsafe', `Path escapes project "${name}": ${relPath}`);
    }
    return target;
  }

  /**
   * Absolute path of project `name`'s specification: spec.jsonc in the project
   * directory, or the file project.jsonc names. A project that has both is
   * refused, so a specification never exists in two copies.
   * @param {string} name
   * @returns {string}
   */
  function specFile(name) {
    const own = resolve(name, WORKSPACE_FILES.spec);
    const config = projectConfig(name);
    if (config === null) return own;
    const spec = config.value.spec;
    // A project.jsonc that only declares roots keeps the specification in the project directory.
    if (spec === undefined && config.value.roots !== undefined) return own;
    if (typeof spec !== 'string' || spec === '' || path.isAbsolute(spec) || !spec.endsWith('.jsonc')) {
      throw new WorkspaceError('project.invalid', `${name}/${PROJECT_FILE} must name the specification as {"spec": "<path relative to the project directory, ending in .jsonc>"}.`);
    }
    let ownExists = true;
    try { readFileSync(own); } catch { ownExists = false; }
    if (ownExists) {
      throw new WorkspaceError('project.invalid', `Project "${name}" has both ${WORKSPACE_FILES.spec} and a ${PROJECT_FILE} naming ${spec}; remove one, so the specification exists once.`);
    }
    return path.resolve(root, name, spec);
  }

  /**
   * project.jsonc of project `name` as parsed JSONC, with the directory relative
   * paths in it resolve against; null when the project has none.
   * @param {string} name
   * @returns {{dir: string, value: Record<string, any>}|null}
   */
  function projectConfig(name) {
    /** @type {string} */ let text;
    try {
      text = readFileSync(resolve(name, PROJECT_FILE), 'utf8');
    } catch (err) {
      const code = /** @type {NodeJS.ErrnoException} */ (err).code;
      if (code === 'ENOENT' || code === 'ENOTDIR') return null;
      throw err;
    }
    const value = parseJsonc(text);
    if (!isPlainObject(value)) {
      throw new WorkspaceError('project.invalid', `${name}/${PROJECT_FILE} must be a JSON object.`);
    }
    return { dir: path.resolve(root, name), value };
  }

  /** The specification's path as shown to people: relative to the directory holding specs/, forward slashes. @param {string} name */
  function specLocation(name) {
    return path.relative(path.dirname(root), specFile(name)).split(path.sep).join('/');
  }

  async function listProjects() {
    let entries;
    try {
      entries = await fs.readdir(root, { withFileTypes: true });
    } catch (err) {
      if (/** @type {NodeJS.ErrnoException} */ (err).code === 'ENOENT') return [];
      throw err;
    }
    const names = entries
      .filter((entry) => entry.isDirectory() && NAME_RE.test(entry.name))
      .map((entry) => entry.name)
      .sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
    const projects = [];
    for (const name of names) {
      const text = await readOptional(specFile(name));
      if (text === null) continue;
      projects.push({ name, title: titleOf(text, name) });
    }
    return projects;
  }

  async function read(name) {
    assertName(name);
    const specText = await readOptional(specFile(name));
    if (specText === null) {
      throw new WorkspaceError('not-found', `Project "${name}" has no specification at ${specLocation(name)}.`);
    }
    const layoutText = await readOptional(resolve(name, WORKSPACE_FILES.layout));
    const recordedText = await readOptional(resolve(name, WORKSPACE_FILES.recorded));
    return {
      spec: { text: specText, hash: hashText(specText), path: specLocation(name) },
      layout: layoutText === null ? null : { text: layoutText, hash: hashText(layoutText) },
      recorded: parseRecorded(recordedText),
    };
  }

  /**
   * @param {string} name
   * @param {'spec'|'layout'} file
   * @param {string} text
   * @param {string|null} baseHash
   * @param {{label?: string, origin?: string}} [meta]
   */
  async function write(name, file, text, baseHash, meta) {
    assertName(name);
    if (file !== 'spec' && file !== 'layout') {
      throw new WorkspaceError('file.unknown', `Unknown file "${String(file)}".`);
    }
    assertText(text);
    const expected = baseHash ?? null;
    if (expected !== null && typeof expected !== 'string') {
      throw new WorkspaceError('input.invalid', 'baseHash must be a string or null.');
    }
    const target = file === 'spec' ? specFile(name) : resolve(name, WORKSPACE_FILES[file]);
    return withProjectLock(projectKey(name), async () => {
      const currentText = await readOptional(target);
      const currentHash = currentText === null ? null : hashText(currentText);
      if (currentHash !== expected) {
        return {
          ok: false,
          conflict: true,
          current: { text: currentText ?? '', hash: currentHash },
        };
      }
      await atomicWrite(target, text);
      const hash = hashText(text);
      // The file is already replaced. A journal line that cannot be appended is reported in the result rather
      // than thrown, so the caller can tell that this write has no journal line. Nothing is rolled back.
      try {
        const journal = resolve(name, JOURNAL_REL);
        const existing = await readOptional(journal);
        const seq =
          (existing === null ? 0 : existing.split('\n').filter((line) => line.trim() !== '').length) + 1;
        const entry = {
          seq,
          file,
          hash,
          baseHash: expected,
          label: meta?.label ?? null,
          origin: meta?.origin ?? null,
          bytes: Buffer.byteLength(text, 'utf8'),
        };
        await fs.mkdir(path.dirname(journal), { recursive: true });
        await fs.appendFile(journal, `${JSON.stringify(entry)}\n`, 'utf8');
        return { ok: true, hash, journal: { written: true, seq } };
      } catch (err) {
        const message = err instanceof Error ? err.message : String(err);
        return { ok: true, hash, journal: { written: false, message: `The journal line was not written: ${message}` } };
      }
    });
  }

  /**
   * @param {string} name
   * @param {Record<string, string>} files keys relative to generated/
   */
  async function writeGenerated(name, files) {
    assertName(name);
    if (!isPlainObject(files)) {
      throw new WorkspaceError('input.invalid', 'files must be an object.');
    }
    const genDir = resolve(name, 'generated');
    const plan = [];
    for (const key of Object.keys(files).sort()) {
      if (key === '' || path.isAbsolute(key) || !/\.(json|md)$/.test(key)) {
        throw new WorkspaceError('path.unsafe', `Generated file must be a relative .json or .md path: ${key}`);
      }
      const target = resolve(name, path.join('generated', key));
      if (!isInside(genDir, target)) {
        throw new WorkspaceError('path.unsafe', `Generated file escapes generated/: ${key}`);
      }
      assertText(files[key], `generated file "${key}"`);
      plan.push({ key, target, content: files[key] });
    }
    return withProjectLock(projectKey(name), async () => {
      const written = [];
      for (const { key, target, content } of plan) {
        if ((await readOptional(target)) === content) continue;
        await atomicWrite(target, content);
        written.push(key);
      }
      return { ok: true, written };
    });
  }

  /** @param {string} name @param {object} object */
  async function writeRecorded(name, object) {
    assertName(name);
    if (!isPlainObject(object)) {
      throw new WorkspaceError('input.invalid', 'Recorded results must be an object.');
    }
    const text = `${JSON.stringify(object, null, 2)}\n`;
    assertText(text, 'recorded results');
    const target = resolve(name, WORKSPACE_FILES.recorded);
    await withProjectLock(projectKey(name), () => atomicWrite(target, text));
    return { ok: true };
  }

  async function exportProject(name) {
    assertName(name);
    const spec = await readOptional(specFile(name));
    if (spec === null) {
      throw new WorkspaceError('not-found', `Project "${name}" has no specification at ${specLocation(name)}.`);
    }
    /** @type {Record<string, string>} */
    const files = { [WORKSPACE_FILES.spec]: spec };
    const layout = await readOptional(resolve(name, WORKSPACE_FILES.layout));
    if (layout !== null) files[WORKSPACE_FILES.layout] = layout;
    const recorded = await readOptional(resolve(name, WORKSPACE_FILES.recorded));
    if (recorded !== null) files[WORKSPACE_FILES.recorded] = recorded;
    return { format: BUNDLE_FORMAT, version: BUNDLE_VERSION, name, files };
  }

  /**
   * Overwrites the project's files present in the bundle. Files absent from the
   * bundle are left alone. Bundle validation problems are returned, not thrown.
   * @param {string} name
   * @param {unknown} bundle
   */
  async function importProject(name, bundle) {
    assertName(name);
    let files;
    try {
      files = validateBundle(bundle);
    } catch (err) {
      if (err instanceof WorkspaceError && (err.code === 'bundle.invalid' || err.code === 'too-large')) {
        return { ok: false, error: err.message };
      }
      throw err;
    }
    const targets = Object.entries(files).map(([key, text]) => ({ target: key === WORKSPACE_FILES.spec ? specFile(name) : resolve(name, key), text }));
    await withProjectLock(projectKey(name), async () => {
      for (const { target, text } of targets) {
        await atomicWrite(target, text);
      }
    });
    return { ok: true };
  }

  /**
   * Watches a project directory. onChange({file, hash}) fires when a tracked file's
   * hash differs from the last hash this subscription saw (own writes included).
   * @param {string} name
   * @param {(change: {file: 'spec'|'layout'|'recorded', hash: string|null}) => void} onChange
   * @returns {() => void} unsubscribe
   */
  function watch(name, onChange) {
    assertName(name);
    const projectDir = path.join(root, name);
    /** @type {string|null} the specification when it lives outside the project directory */
    let external = null;
    try {
      const f = specFile(name);
      if (f !== resolve(name, WORKSPACE_FILES.spec)) external = f;
    } catch {
      // A broken project.jsonc is reported by read(); nothing more to watch.
    }
    const tracked = Object.entries(WORKSPACE_FILES).map(([key, rel]) => ({
      key, rel, abs: key === 'spec' && external ? external : path.join(projectDir, rel), inside: !(key === 'spec' && external),
    }));
    /** @type {Record<string, string|null>} */
    const seen = {};
    for (const { key, abs } of tracked) {
      seen[key] = hashOfFileSync(abs);
    }

    /** @type {Map<string, ReturnType<typeof setTimeout>>} */
    const timers = new Map();
    let closed = false;
    /** @type {import('node:fs').FSWatcher|null} */
    let watcher = null;
    /** @type {import('node:fs').FSWatcher|null} */
    let externalWatcher = null;

    const stop = () => {
      if (closed) return;
      closed = true;
      for (const timer of timers.values()) clearTimeout(timer);
      timers.clear();
      for (const w of [watcher, externalWatcher]) {
        try {
          w?.close();
        } catch {
          // already closed
        }
      }
    };

    const check = async (key, abs) => {
      /** @type {string|null} */ let text = null;
      try {
        text = await fs.readFile(abs, 'utf8');
      } catch {
        text = null;
      }
      if (closed) return;
      const hash = text === null ? null : hashText(text);
      if (hash === seen[key]) return;
      seen[key] = hash;
      onChange({ file: /** @type {'spec'|'layout'|'recorded'} */ (key), hash });
    };

    const schedule = (key, abs) => {
      clearTimeout(timers.get(key));
      timers.set(
        key,
        setTimeout(() => {
          timers.delete(key);
          check(key, abs).catch((err) => console.error('[exegra] watch check failed', err));
        }, DEBOUNCE_MS),
      );
    };

    try {
      watcher = fsWatch(projectDir, { recursive: true }, (_eventType, filename) => {
        if (closed) return;
        const rel = filename == null ? null : String(filename).replace(/\\/g, '/');
        if (rel !== null) {
          const first = rel.split('/')[0];
          if (first === '.history' || first === 'generated' || rel.endsWith('.tmp')) return;
        }
        for (const entry of tracked) {
          if (entry.inside && (rel === null || rel === entry.rel)) schedule(entry.key, entry.abs);
        }
      });
      if (external) {
        const ext = external;
        const base = path.basename(ext);
        // Atomic writes rename a sibling temporary file over the target, so any
        // name starting with the file's own name is a reason to look.
        externalWatcher = fsWatch(path.dirname(ext), (_eventType, filename) => {
          if (closed) return;
          if (filename == null || String(filename).startsWith(base)) schedule('spec', ext);
        });
        externalWatcher.on('error', stop);
      }
    } catch {
      // Project directory missing or unwatchable: nothing to subscribe to.
      stop();
      return stop;
    }
    watcher.on('error', stop);
    return stop;
  }

  return {
    root,
    listProjects,
    read,
    write,
    writeGenerated,
    writeRecorded,
    exportProject,
    importProject,
    watch,
    resolve,
    specFile,
    specLocation,
    projectConfig,
  };
}
