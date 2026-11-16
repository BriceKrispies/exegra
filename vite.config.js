import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vite';
import { exegraDevServer, exegraLinkedSpecs } from './tools/vite-plugin-exegra.js';

const here = path.dirname(fileURLToPath(import.meta.url));

export default defineConfig({
  plugins: [exegraDevServer({ specsDir: path.join(here, 'specs') }), exegraLinkedSpecs({ specsDir: path.join(here, 'specs') })],
  server: {
    host: '127.0.0.1',
    port: 5173,
    strictPort: false,
    // Saving a specification must not trigger a page reload; the app reloads
    // the model itself through the events stream.
    watch: {
      ignored: ['**/specs/**', '**/test-results/**', '**/playwright-report/**'],
    },
    // A linked specification (specs/<name>/project.jsonc) lives in a sibling
    // repository; it is read only through the workspace endpoints.
  },
  build: {
    target: 'es2022',
    outDir: 'dist',
  },
  // The engine worker (src/app/engine-worker.js) loads the WebAssembly glue with a dynamic import,
  // which needs an ES module worker bundle; the default IIFE format cannot split code.
  worker: {
    format: 'es',
  },
});
