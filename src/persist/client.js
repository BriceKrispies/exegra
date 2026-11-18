// Browser side of the local persistence boundary. Talks to the Vite dev-server
// middleware in tools/vite-plugin-exegra.js. Every function reports unavailable
// persistence instead of pretending to save when the app is not under `vite`.

/** True only under the development server; a production build cannot save. */
// Must stay the literal expression `import.meta.env.DEV`: Vite replaces it statically at build time.
// @ts-ignore -- `env` is provided by Vite, not by the ECMAScript ImportMeta type.
export const PERSISTENCE_AVAILABLE = import.meta.env.DEV === true;

const UNAVAILABLE = 'Persistence is only available under the development server.';
const BASE = '/__exegra';

/**
 * The traffic observer (src/app/traffic-recorder.js, installed by the session). The client
 * records the request event of each call that carries a requestId, then the development server's
 * own events for that request (ws-*, then the response or error event), which the server returns in
 * the x-exegra-trace header in the order it produced them. Without an observer nothing is recorded.
 * @typedef {(id: string, payload: Record<string, any>, meta?: {inferred?: boolean}) => void} TrafficObserver
 * @type {TrafficObserver|null}
 */
let observer = null;

/** @param {TrafficObserver|null} fn */
export function observeTraffic(fn) { observer = fn; }

/** @param {string} id @param {Record<string, any>} payload */
function note(id, payload) { if (observer) observer(id, payload); }

/** @param {any} events */
function noteServer(events) {
  if (!observer || !Array.isArray(events)) return;
  for (const e of events) if (e && typeof e.id === 'string') observer(e.id, e.payload ?? {}, e.inferred ? { inferred: true } : undefined);
}

/** @param {Response} res */
function serverTrace(res) {
  const raw = res.headers.get('x-exegra-trace');
  if (!raw) return null;
  try { return JSON.parse(decodeURIComponent(raw)); } catch { return null; }
}

/** @typedef {{requestId?: number}} TrafficOptions */

/**
 * @param {string} method
 * @param {string} path
 * @param {unknown} [body]
 * @param {number} [requestId] correlation id; the server stamps its events with it
 * @returns {Promise<{status: number, data: any}>}
 */
async function request(method, path, body, requestId) {
  /** @type {RequestInit & {headers: Record<string, string>}} */
  const init = { method, headers: { 'x-exegra-client': '1' }, cache: 'no-store' };
  if (typeof requestId === 'number') init.headers['x-exegra-request-id'] = String(requestId);
  if (body !== undefined) {
    init.headers['Content-Type'] = 'application/json';
    init.body = JSON.stringify(body);
  }
  const res = await fetch(`${BASE}${path}`, init);
  if (typeof requestId === 'number') noteServer(serverTrace(res));
  let data = null;
  try {
    data = await res.json();
  } catch {
    data = null;
  }
  return { status: res.status, data };
}

/** @param {{status: number, data: any}} response @returns {any} */
function unwrap({ status, data }) {
  if (status >= 200 && status < 300 && data && data.ok !== false) return data;
  throw new Error(data?.error ?? `Request failed with HTTP ${status}.`);
}

/** @param {unknown} error */
function errorText(error) {
  return error instanceof Error ? error.message : String(error);
}

/** @param {TrafficOptions} [opts] @returns {Promise<{name: string, title: string}[]>} */
export async function listProjects(opts = {}) {
  if (!PERSISTENCE_AVAILABLE) throw new Error(UNAVAILABLE);
  if (typeof opts.requestId === 'number') note('list-projects-request', { requestId: opts.requestId });
  return unwrap(await request('GET', '/projects', undefined, opts.requestId)).projects;
}

/**
 * @param {string} name
 * @param {TrafficOptions} [opts]
 * @returns {Promise<{spec: {text: string, hash: string, path?: string}, layout: {text: string, hash: string}|null, recorded: object|null}>}
 */
export async function readProject(name, opts = {}) {
  if (!PERSISTENCE_AVAILABLE) throw new Error(UNAVAILABLE);
  if (typeof opts.requestId === 'number') note('read-project-request', { name, requestId: opts.requestId });
  return unwrap(await request('GET', `/project?name=${encodeURIComponent(name)}`, undefined, opts.requestId));
}

/**
 * @param {string} name
 * @param {'spec'|'layout'} file
 * @param {string} text
 * @param {string|null} baseHash
 * @param {{label?: string, origin?: string}} [meta]
 * @param {TrafficOptions & {textHash?: string}} [opts] textHash: sha-256 of the text, recorded in place of the text
 * @returns {Promise<{ok: true, hash: string, journal?: {written: boolean, seq?: number, message?: string}} | {ok: false, conflict: true, current: {text: string, hash: string|null}} | {ok: false, error: string}>}
 */
export async function writeFile(name, file, text, baseHash, meta, opts = {}) {
  if (!PERSISTENCE_AVAILABLE) return { ok: false, error: UNAVAILABLE };
  if (typeof opts.requestId === 'number') note('write-file-request', { name, file, text: opts.textHash ?? text, baseHash, requestId: opts.requestId });
  try {
    const { status, data } = await request('POST', '/write', { name, file, text, baseHash, meta }, opts.requestId);
    if (status === 409 && data?.conflict) return data;
    if (status === 200 && data?.ok === true) return data;
    return { ok: false, error: data?.error ?? `Request failed with HTTP ${status}.` };
  } catch (error) {
    return { ok: false, error: errorText(error) };
  }
}

/**
 * @param {string} name
 * @param {Record<string, string>} files keys relative to generated/
 * @param {TrafficOptions & {filesHash?: string}} [opts] filesHash: recorded in place of the files
 * @returns {Promise<{ok: true, written: string[]} | {ok: false, error: string}>}
 */
export async function writeGenerated(name, files, opts = {}) {
  if (!PERSISTENCE_AVAILABLE) return { ok: false, error: UNAVAILABLE };
  if (typeof opts.requestId === 'number') note('generated-write-request', { name, files: opts.filesHash ?? '', requestId: opts.requestId });
  try {
    const { status, data } = await request('POST', '/generated', { name, files }, opts.requestId);
    if (status === 200 && data?.ok === true) return data;
    return { ok: false, error: data?.error ?? `Request failed with HTTP ${status}.` };
  } catch (error) {
    return { ok: false, error: errorText(error) };
  }
}

/**
 * Subscribes to file changes of a project over SSE. The browser re-opens the
 * stream on drop. Returns an unsubscribe function.
 *
 * Unavailable outside the dev server: returns a no-op unsubscribe (this function
 * cannot reject) and never calls onChange.
 *
 * @param {string} name
 * @param {(change: {file: 'spec'|'layout'|'recorded', hash: string|null}) => void} onChange
 * @returns {() => void}
 */
export function watchProject(name, onChange) {
  if (!PERSISTENCE_AVAILABLE) return () => {};
  note('watch-project-request', { name });
  const source = new EventSource(`${BASE}/events?name=${encodeURIComponent(name)}`);
  // The server's own events of this subscription (ws-watch; for each change ws-change and
  // file-change-notice-sent) arrive as "trace" messages just before what they describe.
  source.addEventListener('trace', (event) => {
    try { noteServer(JSON.parse(/** @type {MessageEvent} */ (event).data)); } catch { /* not a trace */ }
  });
  source.addEventListener('change', (event) => {
    let change;
    try {
      change = JSON.parse(/** @type {MessageEvent} */ (event).data);
    } catch {
      return;
    }
    note('external-change-received', { file: change.file, hash: change.hash });
    onChange(change);
  });
  return () => source.close();
}

/** @param {string} name @param {TrafficOptions} [opts] @returns {Promise<object>} */
export async function exportProject(name, opts = {}) {
  if (!PERSISTENCE_AVAILABLE) throw new Error(UNAVAILABLE);
  if (typeof opts.requestId === 'number') note('export-request', { name, requestId: opts.requestId });
  return unwrap(await request('GET', `/export?name=${encodeURIComponent(name)}`, undefined, opts.requestId));
}

/**
 * @param {string} name
 * @param {object} bundle
 * @param {TrafficOptions & {bundleHash?: string}} [opts] bundleHash: sha-256 of the bundle's specification, recorded in place of the bundle
 * @returns {Promise<{ok: boolean, error?: string}>}
 */
export async function importProject(name, bundle, opts = {}) {
  if (!PERSISTENCE_AVAILABLE) return { ok: false, error: UNAVAILABLE };
  if (typeof opts.requestId === 'number') note('import-request', { name, bundle: opts.bundleHash ?? '', requestId: opts.requestId });
  try {
    const { status, data } = await request('POST', '/import', { name, bundle }, opts.requestId);
    if (status === 200 && data?.ok === true) return { ok: true };
    return { ok: false, error: data?.error ?? `Request failed with HTTP ${status}.` };
  } catch (error) {
    return { ok: false, error: errorText(error) };
  }
}
