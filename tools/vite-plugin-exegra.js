// Vite dev-server middleware: a thin HTTP wrapper over tools/workspace.js.
// Development only (apply: 'serve'). It writes files, so every request is
// checked for a loopback Host, a loopback Origin when present, and the
// x-exegra-client header (a non-simple header that cross-site pages cannot send
// without a preflight, which is never granted).

import fs from 'node:fs';
import { createWorkspace, WorkspaceError } from './workspace.js';

const PREFIX = '/__exegra/';
const EVENTS_PATH = '/__exegra/events';
const LOOPBACK = new Set(['localhost', '127.0.0.1', '[::1]']);
const BODY_LIMIT = 20 * 1024 * 1024;
const PING_MS = 25_000;

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
  // Throws WorkspaceError (name.invalid) before any header is sent.
  const unwatch = ws.watch(/** @type {string} */ (url.searchParams.get('name')), ({ file, hash }) => {
    if (!res.writableEnded && !res.destroyed) {
      res.write(`event: change\ndata: ${JSON.stringify({ file, hash })}\n\n`);
    }
  });
  res.writeHead(200, {
    'Content-Type': 'text/event-stream; charset=utf-8',
    'Cache-Control': 'no-store',
    Connection: 'keep-alive',
  });
  res.flushHeaders();
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
 * @param {import('node:http').IncomingMessage} req
 * @param {import('node:http').ServerResponse} res
 * @param {URL} url
 * @param {ReturnType<typeof createWorkspace>} ws
 * @param {Set<{stop: () => void}>} streams
 */
async function route(req, res, url, ws, streams) {
  switch (`${req.method} ${url.pathname}`) {
    case 'GET /__exegra/projects':
      return send(res, 200, { projects: await ws.listProjects() });

    case 'GET /__exegra/project':
      return send(res, 200, await ws.read(url.searchParams.get('name')));

    case 'POST /__exegra/write': {
      const body = await readJsonBody(req);
      const result = await ws.write(body.name, body.file, body.text, body.baseHash, body.meta);
      return send(res, result.ok ? 200 : 409, result);
    }

    case 'POST /__exegra/generated': {
      const body = await readJsonBody(req);
      return send(res, 200, await ws.writeGenerated(body.name, body.files));
    }

    case 'GET /__exegra/export':
      return send(res, 200, await ws.exportProject(url.searchParams.get('name')));

    case 'POST /__exegra/import': {
      const body = await readJsonBody(req);
      const result = await ws.importProject(body.name, body.bundle);
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
          try {
            checkRequest(req, url);
            await route(req, res, url, ws, streams);
          } catch (err) {
            if (res.headersSent) {
              if (!res.writableEnded) res.end();
              return;
            }
            if (err instanceof HttpError) {
              if (err.status === 413) res.setHeader('Connection', 'close');
              return send(res, err.status, { ok: false, error: err.message, code: err.code });
            }
            if (err instanceof WorkspaceError) {
              return send(res, 400, { ok: false, error: err.message, code: err.code });
            }
            server.config.logger.error(`[exegra] ${/** @type {Error} */ (err)?.stack ?? err}`);
            return send(res, 500, { ok: false, error: 'Internal error.', code: 'internal' });
          }
        })();
      });
    },
  };
}
