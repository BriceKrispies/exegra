#!/usr/bin/env node
// Builds the WebAssembly simulation engine into src/engine/pkg/ (generated, not committed). Node-only.
//
//   node tools/build-engine.js        (npm run build:engine)
//
// 1. cargo build --release --target wasm32-unknown-unknown -p exegra-engine-wasm   (in engine/)
// 2. wasm-bindgen --target web --out-dir src/engine/pkg <the .wasm>
//
// Needs Rust stable with the wasm32-unknown-unknown target and wasm-bindgen-cli at exactly the version
// the exegra-engine-wasm crate pins. On Windows the MSVC toolchain is used unless RUSTUP_TOOLCHAIN is
// set. CARGO_TARGET_DIR is honoured. Step 2 is skipped when src/engine/pkg/ is newer than the .wasm.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const ENGINE_DIR = path.join(ROOT, 'engine');
const OUT_DIR = path.join(ROOT, 'src', 'engine', 'pkg');
const CRATE = 'exegra-engine-wasm';
const TARGET = 'wasm32-unknown-unknown';
const OUTPUTS = ['exegra_engine_wasm.js', 'exegra_engine_wasm_bg.wasm'];

/** @param {string} msg */
function fail(msg) {
  process.stderr.write(`build:engine: ${msg}\n`);
  process.exit(1);
}

/** The exact wasm-bindgen version the crate pins ("=x.y.z"). */
function pinnedBindgenVersion() {
  const toml = fs.readFileSync(path.join(ENGINE_DIR, CRATE, 'Cargo.toml'), 'utf8');
  const m = /^wasm-bindgen\s*=\s*"=([0-9.]+)"/m.exec(toml);
  if (!m) fail(`engine/${CRATE}/Cargo.toml must pin wasm-bindgen to an exact version ("=x.y.z").`);
  return /** @type {RegExpExecArray} */ (m)[1];
}

/** @param {string} cmd @param {string[]} args @param {import('node:child_process').SpawnSyncOptions} opts */
function run(cmd, args, opts) {
  const r = spawnSync(cmd, args, { stdio: 'inherit', ...opts });
  if (r.error) fail(`could not run ${cmd}: ${r.error.message}`);
  if (r.status !== 0) fail(`${cmd} ${args.join(' ')} exited with status ${r.status}`);
}

/** @param {string} p */
const mtime = (p) => { try { return fs.statSync(p).mtimeMs; } catch { return -1; } };

function main() {
  /** @type {NodeJS.ProcessEnv} */
  const env = { ...process.env };
  if (process.platform === 'win32' && !env.RUSTUP_TOOLCHAIN) env.RUSTUP_TOOLCHAIN = 'stable-x86_64-pc-windows-msvc';
  if (env.CARGO_BUILD_JOBS === undefined) env.CARGO_BUILD_JOBS = '2';
  if (env.CARGO_BUILD_RUSTC_WRAPPER === undefined) env.CARGO_BUILD_RUSTC_WRAPPER = '';

  run('cargo', ['build', '--release', '--target', TARGET, '-p', CRATE], { cwd: ENGINE_DIR, env });

  const targetDir = env.CARGO_TARGET_DIR ? path.resolve(ENGINE_DIR, env.CARGO_TARGET_DIR) : path.join(ENGINE_DIR, 'target');
  const wasm = path.join(targetDir, TARGET, 'release', 'exegra_engine_wasm.wasm');
  if (!fs.existsSync(wasm)) fail(`cargo did not produce ${wasm}`);

  const built = mtime(wasm);
  if (OUTPUTS.every((f) => mtime(path.join(OUT_DIR, f)) >= built)) {
    process.stdout.write(`build:engine: ${path.relative(ROOT, OUT_DIR).replace(/\\/g, '/')} is up to date\n`);
    return;
  }

  const want = pinnedBindgenVersion();
  const v = spawnSync('wasm-bindgen', ['--version'], { encoding: 'utf8', env });
  if (v.error || v.status !== 0) fail(`wasm-bindgen is not installed. Install it with: cargo install wasm-bindgen-cli --version ${want} --locked`);
  const have = /([0-9]+\.[0-9]+\.[0-9]+)/.exec(v.stdout ?? '')?.[1];
  if (have !== want) fail(`wasm-bindgen ${have ?? '(unknown)'} is installed, but the crate pins ${want}. Install it with: cargo install wasm-bindgen-cli --version ${want} --locked --force`);

  fs.mkdirSync(OUT_DIR, { recursive: true });
  run('wasm-bindgen', ['--target', 'web', '--out-dir', OUT_DIR, wasm], { env });
  process.stdout.write(`build:engine: wrote ${path.relative(ROOT, OUT_DIR).replace(/\\/g, '/')}\n`);
}

main();
