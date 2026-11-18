// Static server for the browser check. Usage: node serve.mjs <wasm build dir> [port=5209]
//   /                 index.html (this directory)
//   /spike/<file>     spike/lean-wasm/<file>  (lean-engine.mjs)
//   /wasm/<file>      the build directory (exegra-lean.mjs, exegra-lean.wasm)
//   /rust/<file>      src/engine/pkg (the Rust engine, for comparison)
//   /goldens/...      tests/conformance/goldens;  /goldens.json  the list of goldens
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const repo = path.resolve(here, '..', '..', '..');
const roots = {
  spike: path.resolve(here, '..'),
  wasm: path.resolve(process.argv[2]),
  rust: path.join(repo, 'src', 'engine', 'pkg'),
  goldens: path.join(repo, 'tests', 'conformance', 'goldens'),
};
const port = Number(process.argv[3] ?? 5209);
const types = { '.html': 'text/html', '.mjs': 'text/javascript', '.js': 'text/javascript', '.wasm': 'application/wasm', '.json': 'application/json' };

function goldens() {
  const out = [];
  for (const source of fs.readdirSync(roots.goldens).sort()) {
    for (const f of fs.readdirSync(path.join(roots.goldens, source)).sort()) {
      if (f.endsWith('.input.json')) out.push(`${source}/${f.slice(0, -'.input.json'.length)}`);
    }
  }
  return out;
}

http.createServer((req, res) => {
  const url = decodeURIComponent(new URL(req.url, 'http://x').pathname);
  let file, base = here;
  if (url === '/') file = path.join(here, 'index.html');
  else if (url === '/goldens.json') { res.writeHead(200, { 'content-type': types['.json'] }); res.end(JSON.stringify(goldens())); return; }
  else {
    const [, root, ...rest] = url.split('/');
    if (roots[root]) { base = roots[root]; file = path.resolve(base, ...rest); }
  }
  if (!file || !file.startsWith(base + path.sep) || !fs.existsSync(file) || fs.statSync(file).isDirectory()) {
    res.writeHead(404); res.end('not found'); return;
  }
  res.writeHead(200, { 'content-type': types[path.extname(file)] ?? 'application/octet-stream', 'cache-control': 'no-store' });
  fs.createReadStream(file).pipe(res);
}).listen(port, '127.0.0.1', () => console.log(`serving on http://127.0.0.1:${port}/`));
