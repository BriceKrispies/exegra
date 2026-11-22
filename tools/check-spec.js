#!/usr/bin/env node
// Check a specification file: diagnostics, claim results and scenario outcomes.
// Usage: node tools/check-spec.js specs/<project>/spec.jsonc [--trace <scenarioId>]
// This is a read-only check (the specification equivalent of a compiler check).

import fs from 'node:fs';
import { analyzeSpec } from '../src/core/analyze.js';
import { evaluateClaims } from '../src/core/claims.js';
import { runScenario } from '../src/core/engine.js';
import { semanticHash } from '../src/core/hash.js';
import { resolveSpecText } from './spec-manifest.js';
import path from 'node:path';

const [file, ...rest] = process.argv.slice(2);
if (!file) {
  console.error('usage: node tools/check-spec.js <spec.jsonc> [--trace <scenarioId>]');
  process.exit(2);
}
const text = resolveSpecText(path.resolve(file), fs.readFileSync(file, 'utf8')).text;
const { model, diagnostics, errorCount } = analyzeSpec(text);

for (const d of diagnostics) {
  console.log(`${d.severity.toUpperCase().padEnd(7)} ${d.loc ? `${d.loc.line}:${d.loc.column}`.padEnd(8) : ''.padEnd(8)} ${d.code}  ${d.message}`);
}
const count = (/** @type {string} */ s) => diagnostics.filter((d) => d.severity === s).length;
console.log(`\n${errorCount} error(s), ${count('warning')} warning(s), ${count('info')} gap(s)`);
if (!model || errorCount) process.exit(1);

console.log(`semantic hash ${semanticHash(model)}`);
console.log('entities: ' + Object.entries(model.byKind).filter(([, v]) => v.length).map(([k, v]) => `${k} ${v.length}`).join(', '));

console.log('\nScenarios:');
for (const s of model.byKind.scenario ?? []) {
  const t = runScenario(model, s.id);
  console.log(`  ${s.id}: ${t.steps.length} steps, outcome ${t.outcome}${t.faults.length ? `, faults ${t.faults.join(', ')}` : ''}`);
}

console.log('\nClaims:');
for (const r of evaluateClaims(model)) {
  console.log(`  [${r.status}] ${r.claimId} (${r.method ?? 'no method'})`);
  console.log(`      ${r.explanation}`);
  if (r.counterexample) console.log(`      counterexample: ${r.counterexample.summary}`);
}

const traceArg = rest.indexOf('--trace');
if (traceArg >= 0 && rest[traceArg + 1]) {
  const t = runScenario(model, rest[traceArg + 1]);
  console.log(`\nTrace of ${t.scenarioId} (${t.outcome}):`);
  for (const st of t.steps) {
    const fired = st.fired.map((f) => `${f.behavior}:${f.from}->${f.to}(${f.transition})`).join(' ');
    console.log(`  #${st.index} t=${st.time} ${st.kind} ${st.event.id} ${fired}${st.error ? ` ERROR ${st.error.message}` : ''}`);
  }
}
