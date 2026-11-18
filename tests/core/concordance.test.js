import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { createWorkspace, hashText } from '../../tools/workspace.js';
import { Project } from '../../src/core/project.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { applyConcordance, sourceNamesSpec } from '../../src/core/concordance.js';

// A specification in another repository, reached through project.jsonc. Its three claims are
// external-evidence claims with no evidence entities, so they are not evaluated until a result exists.
const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "demo", "name": "Demo" },
  "components": [ { "id": "core", "name": "Core", "category": "computational", "purpose": "Runs the demo." } ],
  "claims": [
    { "id": "krn-002", "kind": "structural", "statement": "The core halts.", "subjects": ["core"], "assumptions": [], "evaluate": { "method": "external-evidence" } },
    { "id": "sim-002", "kind": "structural", "statement": "The simulation is deterministic.", "subjects": ["core"], "assumptions": [], "evaluate": { "method": "external-evidence" } },
    { "id": "lone-003", "kind": "structural", "statement": "Nothing records this.", "subjects": ["core"], "assumptions": [], "evaluate": { "method": "external-evidence" } }
  ]
}
`;

/**
 * Runs fn against a specs directory holding project "demo", linked to a specification in a sibling
 * repository. `results` is the text written to the concordance results file; undefined writes no file.
 * @param {string|undefined} results
 * @param {(ws: any, dir: string) => Promise<void>} fn
 * @param {{ omitKey?: boolean }} [config] omitKey: project.jsonc names no results file
 */
async function withLinkedProject(results, fn, config = {}) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'exegra-concordance-'));
  try {
    const specs = path.join(dir, 'specs');
    const demo = path.join(specs, 'demo');
    await fs.mkdir(demo, { recursive: true });
    await fs.mkdir(path.join(dir, 'repo', 'specifications'), { recursive: true });
    await fs.writeFile(path.join(dir, 'repo', 'specifications', 'spec.jsonc'), SPEC, 'utf8');
    const project = { spec: '../../repo/specifications/spec.jsonc' };
    if (!config.omitKey) project.concordanceResults = 'concordance.json';
    await fs.writeFile(path.join(demo, 'project.jsonc'), JSON.stringify(project), 'utf8');
    if (results !== undefined) await fs.writeFile(path.join(demo, 'concordance.json'), results, 'utf8');

    return await fn(createWorkspace(specs), dir);
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
}

/** The claim results of the linked project, with the Concordance results applied as the CLI and the application do. */
async function evaluateLinked(ws) {
  const data = await ws.read('demo');
  const project = new Project({ name: 'demo', specText: data.spec.text, layoutText: null });
  const applied = applyConcordance(project.model, data.recorded, data.concordance);
  const results = evaluateClaims(project.model, { recorded: applied.recorded });
  return { project, data, diagnostics: applied.diagnostics, byId: Object.fromEntries(results.map((r) => [r.claimId, r])) };
}

/** @param {unknown} payload */
const concordance = (payload) => JSON.stringify({ tool: 'concordance', version: '0.1.0', source: 'specifications/spec.jsonc', lint: [], claims: {}, ...(payload && typeof payload === 'object' ? payload : {}) });

test('a Concordance pass makes a requirement supported, never verified', () =>
  withLinkedProject(concordance({
    claims: { 'krn-002': { detail: 'Proved by passing test `krn_002_halts`.', outcome: 'pass', proofs: ['krn_002_halts'], status: 'verified' } },
  }), async (ws) => {
    const { project, byId, diagnostics, data } = await evaluateLinked(ws);
    assert.equal(diagnostics.length, 0);
    assert.equal(byId['krn-002'].status, 'supported');
    assert.notEqual(byId['krn-002'].status, 'verified');
    assert.match(byId['krn-002'].explanation, /Concordance/);
    assert.match(byId['krn-002'].explanation, /krn_002_halts/);
    assert.equal(byId['sim-002'].status, 'not-evaluated');
    // The derived item is evidence of the claim only: not a spec entity, not written back.
    assert.equal((project.model.byKind.evidence ?? []).length, 0);
    assert.equal(data.recorded, null);
  }));

test('a Concordance fail makes a requirement violated', () =>
  withLinkedProject(concordance({
    claims: { 'sim-002': { detail: 'Test failed.', outcome: 'fail', proofs: ['sim_002_repeats'] } },
  }), async (ws) => {
    const { byId, diagnostics } = await evaluateLinked(ws);
    assert.equal(diagnostics.length, 0);
    assert.equal(byId['sim-002'].status, 'violated');
    assert.equal(byId['krn-002'].status, 'not-evaluated');
  }));

test('a claim without a Concordance entry stays not evaluated', () =>
  withLinkedProject(concordance({
    claims: { 'krn-002': { outcome: 'pass' } },
  }), async (ws) => {
    const { byId } = await evaluateLinked(ws);
    assert.equal(byId['lone-003'].status, 'not-evaluated');
    assert.equal(byId['sim-002'].status, 'not-evaluated');
  }));

test('a Concordance file for another tool or specification changes nothing', () =>
  withLinkedProject(undefined, async (ws, dir) => {
    const demo = path.join(dir, 'specs', 'demo');
    const cases = [
      { file: 'other.json', text: concordance({ tool: 'not-concordance', claims: { 'krn-002': { outcome: 'pass' } } }), code: 'concordance.tool' },
      { file: 'other.json', text: concordance({ source: 'elsewhere/spec.jsonc', claims: { 'krn-002': { outcome: 'pass' } } }), code: 'concordance.source' },
      { file: 'other.json', text: '{ not json', code: 'concordance.invalid' },
      { file: 'other.json', text: undefined, code: 'concordance.missing' },
    ];
    for (const c of cases) {
      await fs.writeFile(path.join(demo, 'project.jsonc'), JSON.stringify({ spec: '../../repo/specifications/spec.jsonc', concordanceResults: c.file }), 'utf8');
      if (c.text !== undefined) await fs.writeFile(path.join(demo, c.file), c.text, 'utf8');
      else await fs.rm(path.join(demo, c.file), { force: true });
      const { byId, diagnostics } = await evaluateLinked(ws);
      assert.ok(diagnostics.some((d) => d.code === c.code), `${c.code} reported`);
      for (const id of ['krn-002', 'sim-002', 'lone-003']) assert.equal(byId[id].status, 'not-evaluated', `${id} with ${c.code}`);
    }
    assert.equal(sourceNamesSpec('specifications/spec.jsonc', path.join(dir, 'repo', 'specifications', 'spec.jsonc')), true);
    assert.equal(sourceNamesSpec('spec.jsonc', path.join(dir, 'repo', 'specifications', 'spec.jsonc')), true);
    assert.equal(sourceNamesSpec('ecifications/spec.jsonc', path.join(dir, 'repo', 'specifications', 'spec.jsonc')), false);
  }));

test('an unknown claim id is a warning and the other entries still apply', () =>
  withLinkedProject(concordance({
    claims: { 'no-such-claim': { outcome: 'pass' }, 'krn-002': { outcome: 'pass' } },
  }), async (ws) => {
    const { byId, diagnostics } = await evaluateLinked(ws);
    const warning = diagnostics.find((d) => d.code === 'concordance.claim');
    assert.ok(warning, 'unknown claim reported');
    assert.equal(warning.severity, 'warning');
    assert.match(warning.message, /no-such-claim/);
    assert.equal(byId['krn-002'].status, 'supported');
    assert.equal(byId['sim-002'].status, 'not-evaluated');
  }));

test('a project without concordanceResults is unchanged', () =>
  withLinkedProject(concordance({ claims: { 'krn-002': { outcome: 'pass' } } }), async (ws) => {
    const data = await ws.read('demo');
    assert.equal(data.concordance, null);
    const project = new Project({ name: 'demo', specText: data.spec.text, layoutText: null });
    const applied = applyConcordance(project.model, data.recorded, data.concordance);
    assert.equal(applied.recorded, data.recorded);
    assert.deepEqual(applied.diagnostics, []);
    const plain = evaluateClaims(project.model, { recorded: data.recorded ?? undefined });
    assert.ok(plain.every((r) => r.status === 'not-evaluated'));
  }, { omitKey: true }));

test('a results file naming the current specification text is applied with its revision matched', () =>
  withLinkedProject(concordance({ specSha256: hashText(SPEC), claims: { 'krn-002': { outcome: 'pass', detail: 'ok' } } }), async (ws) => {
    const { byId, diagnostics } = await evaluateLinked(ws);
    assert.equal(diagnostics.length, 0);
    assert.equal(byId['krn-002'].status, 'supported');
    assert.doesNotMatch(byId['krn-002'].explanation, /unknown revision/);
  }));

test('a results file naming another specification text is not applied', () =>
  withLinkedProject(concordance({ specSha256: '0'.repeat(64), claims: { 'krn-002': { outcome: 'pass' } } }), async (ws) => {
    const { byId, diagnostics } = await evaluateLinked(ws);
    assert.ok(diagnostics.some((d) => d.code === 'concordance.revision'), 'revision reported');
    assert.equal(byId['krn-002'].status, 'not-evaluated');
  }));

test('a results file that names no specification text is applied, and the result says the revision is unknown', () =>
  withLinkedProject(concordance({ claims: { 'krn-002': { outcome: 'pass' } } }), async (ws) => {
    const { byId, diagnostics } = await evaluateLinked(ws);
    assert.equal(diagnostics.length, 0);
    assert.equal(byId['krn-002'].status, 'supported');
    assert.match(byId['krn-002'].explanation, /unknown revision of the specification/);
  }));

test('a results path that is a directory is a warning and not a load failure', () =>
  withLinkedProject(undefined, async (ws, dir) => {
    await fs.mkdir(path.join(dir, 'specs', 'demo', 'concordance.json'));
    const { byId, diagnostics } = await evaluateLinked(ws);
    const d = diagnostics.find((x) => x.code === 'concordance.unreadable');
    assert.ok(d, 'reported');
    assert.equal(d.severity, 'warning');
    assert.match(d.message, /is a directory/);
    for (const id of ['krn-002', 'sim-002', 'lone-003']) assert.equal(byId[id].status, 'not-evaluated');
  }));

test('watching a project reports a change to its Concordance results file as a change of the recorded results', () =>
  withLinkedProject(concordance({ claims: { 'krn-002': { outcome: 'pass' } } }), async (ws, dir) => {
    const changes = [];
    const stop = ws.watch('demo', (c) => changes.push(c));
    try {
      await new Promise((r) => setTimeout(r, 50));
      const next = concordance({ claims: { 'krn-002': { outcome: 'fail' } } });
      await fs.writeFile(path.join(dir, 'specs', 'demo', 'concordance.json'), next, 'utf8');
      for (let i = 0; i < 40 && !changes.length; i++) await new Promise((r) => setTimeout(r, 50));
      assert.equal(changes[0]?.file, 'recorded');
      assert.equal(changes[0]?.hash, hashText(next));
    } finally {
      stop();
    }
  }));
