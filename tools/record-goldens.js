#!/usr/bin/env node
// Records the conformance goldens (tests/conformance/goldens) with the simulation engine (src/core/engine.js,
// the WebAssembly build of engine/; build it first with npm run build:engine). Deterministic: running it twice
// gives identical files. Node-only.
//
//   node tools/record-goldens.js            write goldens that do not exist yet; never overwrite an existing one
//                                           (exit 1, listing every existing golden the engine no longer reproduces)
//   node tools/record-goldens.js --force    rewrite every golden and remove files that no longer correspond to one
//
// The committed goldens are the reference an engine is judged against: re-record them only on purpose, for a
// deliberate change of the simulation semantics or of the specifications they are recorded from.
//
// For each source specification and each scenario it records, as <source>/<name>.input.json and
// <name>.trace.json (only the input when the engine refuses it as ill-typed or non-integer):
//   <scenario>               the scenario with its own declared faults
//   <scenario>--none         with no faults, when the scenario declares any
//   <scenario>--<fault>      with that one fault, when the scenario declares more than one
// With --force, files that no longer correspond to a golden are removed.

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../src/core/analyze.js';
import { stableStringify } from '../src/core/stable-json.js';
import { initEngine, runScenario } from '../src/core/engine.js';
import { simulationInput } from '../src/core/sim-input.js';
import { ELAB_REFUSAL, GOLDENS_DIR, REPO_ROOT } from './conformance.js';
import { readSpecFile } from './spec-manifest.js';

/** The specifications the goldens are recorded from: [source name, path relative to the repository root]. */
export const SOURCES = [
  ['fixture', 'tests/conformance/fixture/spec.jsonc'],
  ['exegra', 'specs/exegra/spec.jsonc'],
  ['multiplayer', 'tests/fixtures/multiplayer/spec.jsonc'],
];

/**
 * @typedef {import('../src/core/types.js').Model} Model
 * @typedef {{name:string, scenarioId:string, faults:string[]|undefined}} Variant
 */

/**
 * The runs recorded for one scenario.
 * @param {Model} model @param {string} scenarioId
 * @returns {Variant[]}
 */
export function variantsOf(model, scenarioId) {
  const own = /** @type {string[]} */ ([...new Set(model.entities.get(scenarioId)?.data.faults ?? [])]);
  /** @type {Variant[]} */
  const out = [{ name: scenarioId, scenarioId, faults: undefined }];
  if (own.length) out.push({ name: `${scenarioId}--none`, scenarioId, faults: [] });
  if (own.length > 1) for (const f of own) out.push({ name: `${scenarioId}--${f}`, scenarioId, faults: [f] });
  return out;
}

/** @param {any} value */
const toJson = (value) => `${stableStringify(value, 1)}\n`;

/** @param {string} source @param {string} file */
export function loadModel(source, file) {
  const { model, errorCount, diagnostics } = analyzeSpec(readSpecFile(path.join(REPO_ROOT, file)));
  if (!model || errorCount) {
    const msgs = diagnostics.filter((d) => d.severity === 'error').map((d) => d.message).join('; ');
    throw new Error(`${source} (${file}) has errors: ${msgs}`);
  }
  return model;
}

const USAGE = `Usage: node tools/record-goldens.js [--force]
  Writes tests/conformance/goldens/<source>/<scenario>.{input,trace}.json with the simulation engine.
  Without --force it writes only goldens that do not exist yet. It refuses to overwrite an existing golden:
  one the engine no longer reproduces is listed and left unchanged, and the exit status is 1.
  --force   rewrite every golden and remove files that no longer correspond to one.
`;

/** @param {string} p */
const rel = (p) => path.relative(REPO_ROOT, p).replace(/\\/g, '/');

/** @param {string[]} argv @returns {number} exit code */
function main(argv) {
  let force = false;
  for (const a of argv) {
    if (a === '--force') force = true;
    else if (a === '--help' || a === '-h') { process.stdout.write(USAGE); return 0; }
    else { process.stderr.write(`Unknown argument "${a}".\n${USAGE}`); return 2; }
  }
  initEngine();
  /** @type {{path:string, text:string}[]} */
  const writes = [];
  /** @type {string[]} */
  const removals = [];
  /** @type {Record<string, number>} */
  const counts = {};
  for (const [source, file] of SOURCES) {
    const model = loadModel(source, file);
    const dir = path.join(GOLDENS_DIR, source);
    const wanted = new Set();
    counts[source] = 0;
    for (const scenario of model.byKind.scenario ?? []) {
      for (const v of variantsOf(model, scenario.id)) {
        const input = simulationInput(model, v.scenarioId, v.faults);
        // An input the engine refuses as ill-typed or non-integer has no trace golden (WG-5681).
        /** @type {any} */
        let trace = null;
        try {
          trace = runScenario(model, v.scenarioId, v.faults === undefined ? undefined : { faults: v.faults });
        } catch (e) {
          if (!ELAB_REFUSAL.test(/** @type {Error} */ (e).message)) throw e;
        }
        for (const [suffix, value] of trace === null ? [['input', input]] : [['input', input], ['trace', trace]]) {
          const name = `${v.name}.${suffix}.json`;
          wanted.add(name);
          writes.push({ path: path.join(dir, name), text: toJson(value) });
        }
        counts[source]++;
      }
    }
    if (fs.existsSync(dir)) for (const f of fs.readdirSync(dir)) if (!wanted.has(f)) removals.push(path.join(dir, f));
  }
  if (fs.existsSync(GOLDENS_DIR)) {
    for (const d of fs.readdirSync(GOLDENS_DIR)) {
      const full = path.join(GOLDENS_DIR, d);
      if (!SOURCES.some(([s]) => s === d) && fs.statSync(full).isDirectory()) removals.push(full);
    }
  }
  // Without --force an existing golden is never written: it is left as it is, and reported when it differs.
  const existing = force ? [] : writes.filter((w) => fs.existsSync(w.path));
  const differing = existing.filter((w) => fs.readFileSync(w.path, 'utf8') !== w.text);
  let written = 0;
  for (const w of writes) {
    if (existing.includes(w)) continue;
    fs.mkdirSync(path.dirname(w.path), { recursive: true });
    fs.writeFileSync(w.path, w.text, 'utf8');
    written++;
  }
  if (force) for (const r of removals) fs.rmSync(r, { recursive: true, force: true });
  else if (removals.length) process.stdout.write(`record-goldens: kept ${removals.length} file(s) that no longer correspond to a golden (--force removes them)\n`);
  process.stdout.write(`${Object.entries(counts).map(([s, n]) => `${n} ${s}`).join(', ')} goldens in ${rel(GOLDENS_DIR)}: wrote ${written} file(s)${force ? '' : `, left ${existing.length} existing file(s) unchanged`}\n`);
  if (differing.length) {
    process.stderr.write(`record-goldens: refused to overwrite ${differing.length} existing golden file(s) that the engine no longer reproduces:\n`
      + differing.map((w) => `  ${rel(w.path)}\n`).join('')
      + 'The committed goldens are the reference engines are judged against. Pass --force to re-record them on purpose.\n');
    return 1;
  }
  return 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) process.exitCode = main(process.argv.slice(2));
