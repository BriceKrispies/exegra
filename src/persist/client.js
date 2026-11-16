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
 * @param {string} method
 * @param {string} path
 * @param {unknown} [body]
 * @returns {Promise<{status: number, data: any}>}
 */
async function request(method, path, body) {
  /** @type {RequestInit & {headers: Record<string, string>}} */
  const init = { method, headers: { 'x-exegra-client': '1' }, cache: 'no-store' };
  if (body !== undefined) {
    init.headers['Content-Type'] = 'application/json';
    init.body = JSON.stringify(body);
  }
  const res = await fetch(`${BASE}${path}`, init);
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

/** @returns {Promise<{name: string, title: string}[]>} */
export async function listProjects() {
  if (!PERSISTENCE_AVAILABLE) throw new Error(UNAVAILABLE);
  return unwrap(await request('GET', '/projects')).projects;
}

/**
 * @param {string} name
 * @returns {Promise<{spec: {text: string, hash: string, path?: string}, layout: {text: string, hash: string}|null, recorded: object|null}>}
 */
export async function readProject(name) {
  if (!PERSISTENCE_AVAILABLE) throw new Error(UNAVAILABLE);
  return unwrap(await request('GET', `/project?name=${encodeURIComponent(name)}`));
}

/**
 * @param {string} name
 * @param {'spec'|'layout'} file
 * @param {string} text
 * @param {string|null} baseHash
 * @param {{label?: string, origin?: string}} [meta]
 * @returns {Promise<{ok: true, hash: string} | {ok: false, conflict: true, current: {text: string, hash: string|null}} | {ok: false, error: string}>}
 */
export async function writeFile(name, file, text, baseHash, meta) {
  if (!PERSISTENCE_AVAILABLE) return { ok: false, error: UNAVAILABLE };
  try {
    const { status, data } = await request('POST', '/write', { name, file, text, baseHash, meta });
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
 * @returns {Promise<{ok: true, written: string[]} | {ok: false, error: string}>}
 */
export async function writeGenerated(name, files) {
  if (!PERSISTENCE_AVAILABLE) return { ok: false, error: UNAVAILABLE };
  try {
    const { status, data } = await request('POST', '/generated', { name, files });
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
  const source = new EventSource(`${BASE}/events?name=${encodeURIComponent(name)}`);
  source.addEventListener('change', (event) => {
    let change;
    try {
      change = JSON.parse(/** @type {MessageEvent} */ (event).data);
    } catch {
      return;
    }
    onChange(change);
  });
  return () => source.close();
}

/** @param {string} name @returns {Promise<object>} */
export async function exportProject(name) {
  if (!PERSISTENCE_AVAILABLE) throw new Error(UNAVAILABLE);
  return unwrap(await request('GET', `/export?name=${encodeURIComponent(name)}`));
}

/**
 * @param {string} name
 * @param {object} bundle
 * @returns {Promise<{ok: boolean, error?: string}>}
 */
export async function importProject(name, bundle) {
  if (!PERSISTENCE_AVAILABLE) return { ok: false, error: UNAVAILABLE };
  try {
    const { status, data } = await request('POST', '/import', { name, bundle });
    if (status === 200 && data?.ok === true) return { ok: true };
    return { ok: false, error: data?.error ?? `Request failed with HTTP ${status}.` };
  } catch (error) {
    return { ok: false, error: errorText(error) };
  }
}
