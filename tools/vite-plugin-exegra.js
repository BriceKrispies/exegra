// Vite dev-server middleware: a thin HTTP wrapper over tools/workspace.js.
// Development only (apply: 'serve'). It writes files, so every request is
// checked for a loopback Host, a loopback Origin when present, and the
// x-exegra-client header (a non-simple header that cross-site pages cannot send
// without a preflight, which is never granted).

import fs from 'node:fs';
import { createWorkspace, WorkspaceError, hashText } from './workspace.js';

const PREFIX = '/__exegra/';
const EVENTS_PATH = '/__exegra/events';
const LOOPBACK = new Set(['localhost', '127.0.0.1', '[::1]']);
const BODY_LIMIT = 20 * 1024 * 1024;
const PING_MS = 25_000;

// ---- traffic (WG-4777) ------------------------------------------------------------------------
// The server's own events, named by the event ids of specs/exegra/spec.jsonc, so that the running
// application can replay them through its self-model (src/core/replay.js). A request that carries
// x-exegra-request-id gets its events back in the x-exegra-trace header (URI-encoded JSON), in the
// order the server produced them; the persistence client appends them to its traffic record. Texts
// are recorded as their sha-256, as the self-model represents them. Nothing is kept on the server
// beyond the hashes it wrote itself (to tell its own writes from external edits in change notices).

/** @typedef {{id: string, payload: Record<string, any>, inferred?: boolean}} ServerEvent */
/** @typedef {{requestId: number|null, events: ServerEvent[], add: (id: string, payload: Record<string, any>, inferred?: boolean) => void}} ServerTrace */

/** @type {WeakMap<import('node:http').ServerResponse, ServerTrace>} */
const TRACES = new WeakMap();

/** @param {import('node:http').IncomingMessage} req @param {import('node:http').ServerResponse} res @returns {ServerTrace} */
function startTrace(req, res) {
  const raw = Number(req.headers['x-exegra-request-id']);
  const requestId = Number.isInteger(raw) ? raw : null;
  /** @type {ServerTrace} */
  const trace = {
    requestId,
    events: [],
    add(id, payload, inferred) {
      if (requestId === null) return;
      trace.events.push(inferred ? { id, payload, inferred: true } : { id, payload });
    },
  };
  TRACES.set(res, trace);
  return trace;
}

/** The error event of each route, for an answer that is not a success. */
const ERROR_EVENTS = {
  '/__exegra/write': 'write-file-failed',
  '/__exegra/project': 'read-project-failed',
  '/__exegra/export': 'export-failed',
  '/__exegra/import': 'import-refused',
};

/** sha-256 of a JSON value with sorted object keys (the generated files of one request). @param {any} v */
export function hashFiles(v) {
  const sort = (/** @type {any} */ x) => (x && typeof x === 'object' && !Array.isArray(x) ? Object.fromEntries(Object.keys(x).sort().map((k) => [k, sort(x[k])])) : x);
  return hashText(JSON.stringify(sort(v ?? {})));
}

/** @param {unknown} text */
const textHash = (text) => (typeof text === 'string' ? hashText(text) : text ?? null);

/** Hashes this server wrote, per project file, so a change notice can tell its own writes from external edits. */
const OWN_WRITES = new Map();
/** @param {string} name @param {string} file @param {string} hash */
function rememberWrite(name, file, hash) {
  const key = `${name}/${file}`;
  const list = OWN_WRITES.get(key) ?? [];
  list.push(hash);
  if (list.length > 32) list.shift();
  OWN_WRITES.set(key, list);
}

class HttpError extends Error {
  /**
   * @param {number} status
   * @param {string} code
   * @param {string} message
   */
  constructor(status, code, message) {
    super(message);
    this.status = status;
    this.code = code;
  }
}

/** @param {string|undefined} host @returns {string|null} */
function hostnameOf(host) {
  if (typeof host !== 'string') return null;
  try {
    return new URL(`http://${host}`).hostname;
  } catch {
    return null;
  }
}

/** @param {string|undefined} origin @returns {string|null} */
function originHostname(origin) {
  if (typeof origin !== 'string') return null;
  try {
    return new URL(origin).hostname;
  } catch {
    return null;
  }
}

/** @param {import('node:http').IncomingMessage} req */
function checkRequest(req, url) {
  const host = hostnameOf(req.headers.host);
  if (host === null || !LOOPBACK.has(host)) {
    throw new HttpError(403, 'host.forbidden', 'Exegra endpoints accept loopback hosts only.');
  }
  if (req.headers.origin !== undefined) {
    const origin = originHostname(req.headers.origin);
    if (origin === null || !LOOPBACK.has(origin)) {
      throw new HttpError(403, 'origin.forbidden', 'Cross-origin requests are not allowed.');
    }
  }
  const isEvents = req.method === 'GET' && url.pathname === EVENTS_PATH;
  if (!isEvents && req.headers['x-exegra-client'] !== '1') {
    throw new HttpError(403, 'client.header', 'Missing x-exegra-client header.');
  }
}

/** @param {import('node:http').ServerResponse} res @param {number} status @param {unknown} body */
function send(res, status, body) {
  const trace = TRACES.get(res);
  if (trace && trace.events.length) res.setHeader('x-exegra-trace', encodeURIComponent(JSON.stringify(trace.events)));
  res.statusCode = status;
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  res.setHeader('Cache-Control', 'no-store');
  res.end(JSON.stringify(body));
}

/** @param {import('node:http').IncomingMessage} req @returns {Promise<string>} */
function readBody(req) {
  return new Promise((resolve, reject) => {
    /** @type {Buffer[]} */
    const chunks = [];
    let size = 0;
    let done = false;
    req.on('data', (chunk) => {
      if (done) return;
      size += chunk.length;
      if (size > BODY_LIMIT) {
        done = true;
        reject(new HttpError(413, 'body.too-large', 'Request body is larger than 20 MB.'));
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => {
      if (done) return;
      done = true;
      resolve(Buffer.concat(chunks).toString('utf8'));
    });
    req.on('error', (err) => {
      if (done) return;
      done = true;
      reject(err);
    });
  });
}

/** @param {import('node:http').IncomingMessage} req @returns {Promise<Record<string, any>>} */
async function readJsonBody(req) {
  const text = await readBody(req);
  let parsed;
  try {
    parsed = JSON.parse(text);
  } catch {
    throw new HttpError(400, 'body.invalid', 'Request body is not valid JSON.');
  }
  if (parsed === null || typeof parsed !== 'object' || Array.isArray(parsed)) {
    throw new HttpError(400, 'body.invalid', 'Request body must be a JSON object.');
  }
  return parsed;
}

/**
 * Opens a text/event-stream for project changes. Registers the stream so the
 * server can close it on shutdown.
 * @param {import('node:http').IncomingMessage} req
 * @param {import('node:http').ServerResponse} res
 * @param {URL} url
 * @param {ReturnType<typeof createWorkspace>} ws
 * @param {Set<{stop: () => void}>} streams
 */
function openEvents(req, res, url, ws, streams) {
  const name = /** @type {string} */ (url.searchParams.get('name'));
  // Throws WorkspaceError (name.invalid) before any header is sent.
  const unwatch = ws.watch(name, ({ file, hash }) => {
    if (!res.writableEnded && !res.destroyed) {
      res.write(`event: trace\ndata: ${JSON.stringify(changeTrace(name, file, hash))}\n\n`);
      res.write(`event: change\ndata: ${JSON.stringify({ file, hash })}\n\n`);
    }
  });
  res.writeHead(200, {
    'Content-Type': 'text/event-stream; charset=utf-8',
    'Cache-Control': 'no-store',
    Connection: 'keep-alive',
  });
  res.flushHeaders();
  res.write(`event: trace\ndata: ${JSON.stringify([{ id: 'ws-watch', payload: { name } }])}\n\n`);
  const ping = setInterval(() => {
    if (!res.destroyed) res.write(': ping\n\n');
  }, PING_MS);
  let stopped = false;
  const stream = {
    stop() {
      if (stopped) return;
      stopped = true;
      clearInterval(ping);
      unwatch();
      streams.delete(stream);
      if (!res.writableEnded) res.end();
    },
  };
  streams.add(stream);
  res.on('close', () => stream.stop());
}

/**
 * The server events of one change notice. A hash this server wrote is its own write, whose
 * disk-file-replaced was recorded with the write; any other hash is an external edit, which the
 * server infers (marked inferred): the file was replaced by another process.
 * @param {string} name @param {'spec'|'layout'|'recorded'} file @param {string|null} hash
 * @returns {ServerEvent[]}
 */
export function changeTrace(name, file, hash) {
  /** @type {ServerEvent[]} */
  const out = [];
  const own = hash !== null && (OWN_WRITES.get(`${name}/${file}`) ?? []).includes(hash);
  if (!own && hash !== null) {
    if (file === 'recorded') {
      out.push({ id: 'ws-write-recorded', payload: { version: hash }, inferred: true });
      out.push({ id: 'disk-file-replaced', payload: { file, hash }, inferred: true });
      out.push({ id: 'ws-recorded-done', payload: { version: hash }, inferred: true });
    } else {
      out.push({ id: 'disk-edited-externally', payload: { file, hash }, inferred: true });
      out.push({ id: 'disk-file-replaced', payload: { file, hash }, inferred: true });
    }
  }
  out.push({ id: 'ws-change', payload: { file, hash } });
  out.push({ id: 'file-change-notice-sent', payload: { file, hash } });
  return out;
}

/** @param {ReturnType<typeof createWorkspace>} ws @param {string} name */
function recordedHash(ws, name) {
  try { return hashText(fs.readFileSync(ws.resolve(name, 'evidence/results.json'), 'utf8')); } catch { return null; }
}

/**
 * @param {import('node:http').IncomingMessage} req
 * @param {import('node:http').ServerResponse} res
 * @param {URL} url
 * @param {ReturnType<typeof createWorkspace>} ws
 * @param {Set<{stop: () => void}>} streams
 */
async function route(req, res, url, ws, streams) {
  const t = TRACES.get(res) ?? startTrace(req, res);
  const requestId = t.requestId;
  switch (`${req.method} ${url.pathname}`) {
    case 'GET /__exegra/projects': {
      t.add('ws-list', { requestId });
      const projects = await ws.listProjects();
      const names = projects.map((p) => p.name);
      t.add('ws-list-done', { projects: names, requestId });
      t.add('list-projects-ok', { projects: names, requestId });
      return send(res, 200, { projects });
    }

    case 'GET /__exegra/project': {
      const name = url.searchParams.get('name');
      t.add('ws-read', { name, caller: 'http', requestId });
      let files;
      try {
        files = await ws.read(name);
      } catch (err) {
        if (err instanceof WorkspaceError && err.code === 'not-found') t.add('ws-read-missing', { caller: 'http', requestId });
        throw err;
      }
      const shape = { spec: files.spec.hash, layout: files.layout?.hash ?? null, recorded: files.recorded === null ? null : recordedHash(ws, /** @type {string} */ (name)) };
      t.add('ws-read-done', { ...shape, caller: 'http', requestId });
      t.add('read-project-ok', { ...shape, requestId });
      return send(res, 200, files);
    }

    case 'POST /__exegra/write': {
      const body = await readJsonBody(req);
      t.add('ws-write', { name: body.name, file: body.file, text: textHash(body.text), baseHash: body.baseHash ?? null, caller: 'http', requestId });
      const result = await ws.write(body.name, body.file, body.text, body.baseHash, body.meta);
      if (result.ok) {
        rememberWrite(body.name, body.file, /** @type {string} */ (result.hash));
        t.add('disk-file-replaced', { file: body.file, hash: result.hash });
        t.add('ws-write-done', { file: body.file, hash: result.hash, caller: 'http', requestId });
        t.add('write-file-ok', { ok: true, hash: result.hash, requestId });
      } else if ('conflict' in result && result.conflict) {
        t.add('ws-write-conflict', { file: body.file, current: result.current.hash, caller: 'http', requestId });
        t.add('write-file-conflict', { code: 'conflict', current: result.current.hash, requestId });
      }
      return send(res, result.ok ? 200 : 409, result);
    }

    case 'POST /__exegra/generated': {
      const body = await readJsonBody(req);
      t.add('ws-write-generated', { name: body.name, files: hashFiles(body.files), caller: 'http', requestId });
      const result = await ws.writeGenerated(body.name, body.files);
      t.add('ws-generated-done', { written: result.written, caller: 'http', requestId });
      t.add('generated-write-ok', { ok: true, written: result.written, requestId });
      return send(res, 200, result);
    }

    case 'GET /__exegra/export': {
      const name = url.searchParams.get('name');
      t.add('ws-export', { name, requestId });
      let bundle;
      try {
        bundle = await ws.exportProject(name);
      } catch (err) {
        if (err instanceof WorkspaceError && err.code === 'not-found') t.add('ws-export-missing', { requestId });
        throw err;
      }
      const files = hashText(bundle.files['spec.jsonc']);
      t.add('ws-export-done', { name, files, requestId });
      t.add('export-ok', { format: bundle.format, version: bundle.version, name, files, requestId });
      return send(res, 200, bundle);
    }

    case 'POST /__exegra/import': {
      const body = await readJsonBody(req);
      const specText = body.bundle?.files?.['spec.jsonc'];
      const bundleHash = typeof specText === 'string' ? hashText(specText) : '';
      t.add('ws-import', { name: body.name, bundle: bundleHash, requestId });
      const result = await ws.importProject(body.name, body.bundle);
      if (result.ok) {
        rememberWrite(body.name, 'spec', bundleHash);
        t.add('disk-file-replaced', { file: 'spec', hash: bundleHash });
        t.add('ws-import-done', { requestId });
        t.add('import-ok', { ok: true, requestId });
      } else {
        t.add('ws-import-refused', { requestId });
        t.add('import-refused', { code: 'bundle.invalid', requestId });
      }
      return send(res, result.ok ? 200 : 400, result);
    }

    case `GET ${EVENTS_PATH}`:
      return openEvents(req, res, url, ws, streams);

    default:
      throw new HttpError(404, 'route.unknown', 'Unknown Exegra endpoint.');
  }
}

const LINKED_ID = 'virtual:exegra-linked-specs';

/**
 * Projects whose specification lives outside specs/ (named by project.jsonc)
 * are not matched by the application's import.meta.glob. In a production build
 * this module supplies their text, keyed by project name; during development it
 * is empty, because the application then reads every project through the
 * workspace endpoints.
 * @param {{specsDir: string}} options
 */
export function exegraLinkedSpecs({ specsDir }) {
  const ws = createWorkspace(specsDir);
  let build = false;
  return {
    name: 'exegra-linked-specs',
    /** @param {{command: string}} config */
    configResolved(config) { build = config.command === 'build'; },
    /** @param {string} id */
    resolveId(id) { return id === LINKED_ID ? '\0' + LINKED_ID : null; },
    /** @param {string} id */
    async load(id) {
      if (id !== '\0' + LINKED_ID) return null;
      /** @type {Record<string, string>} */
      const linked = {};
      if (build) {
        for (const { name } of await ws.listProjects()) {
          const file = ws.specFile(name);
          if (file !== ws.resolve(name, 'spec.jsonc')) linked[name] = fs.readFileSync(file, 'utf8');
        }
      }
      return `export default ${JSON.stringify(linked)};`;
    },
  };
}

/**
 * @param {{specsDir: string}} options specsDir: absolute path of the `specs` directory
 */
export function exegraDevServer({ specsDir }) {
  const ws = createWorkspace(specsDir);
  return {
    name: 'exegra-dev-server',
    apply: 'serve',
    configureServer(server) {
      /** @type {Set<{stop: () => void}>} */
      const streams = new Set();
      server.httpServer?.once('close', () => {
        for (const stream of [...streams]) stream.stop();
      });

      server.middlewares.use((req, res, next) => {
        const url = new URL(req.url ?? '/', 'http://localhost');
        if (!url.pathname.startsWith(PREFIX)) return next();
        (async () => {
          const trace = startTrace(req, res);
          /** @param {string} code */
          const failed = (code) => {
            const id = ERROR_EVENTS[/** @type {keyof typeof ERROR_EVENTS} */ (url.pathname)];
            if (id) trace.add(id, { code, requestId: trace.requestId });
          };
          try {
            checkRequest(req, url);
            await route(req, res, url, ws, streams);
          } catch (err) {
            if (res.headersSent) {
              if (!res.writableEnded) res.end();
              return;
            }
            if (err instanceof HttpError) {
              failed(err.code);
              if (err.status === 413) res.setHeader('Connection', 'close');
              return send(res, err.status, { ok: false, error: err.message, code: err.code });
            }
            if (err instanceof WorkspaceError) {
              failed(err.code);
              return send(res, 400, { ok: false, error: err.message, code: err.code });
            }
            server.config.logger.error(`[exegra] ${/** @type {Error} */ (err)?.stack ?? err}`);
            failed('internal');
            return send(res, 500, { ok: false, error: 'Internal error.', code: 'internal' });
          }
        })();
      });
    },
  };
}
