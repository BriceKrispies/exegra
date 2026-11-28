// The shipped application's model of the self-specification is the one the command line derives (WG-5704, M4): the
// production bundle holds the resolved specification and the extracted facts, and a session built from them has the
// semantic hash and the derived interactions `exegra derive` reports. A build equivalence, so it runs with the proofs
// (npm run test:proofs, npm run verify, the Check workflow).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

// The build's bundled specification (the resolved manifest) with the bundled fact file gives the semantic hash and the L1 interactions the command line gives, so the read-only application draws the same derived model.
// @evidence navigation-scene-is-derived-model #
test('a production build bundles the self-specification resolved and the shipped application derives the CLI model from it', async () => {
  const { spawnSync } = await import('node:child_process');
  const { exegraLinkedSpecs } = await import('../../tools/vite-plugin-exegra.js');
  const { Project } = await import('../../src/core/project.js');
  const { deriveModel } = await import('../../src/core/abstraction.js');
  const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
  const specsDir = path.join(root, 'specs');
  // The plugin as vite build runs it: the virtual module of bundled specifications.
  const plugin = exegraLinkedSpecs({ specsDir });
  plugin.configResolved({ command: 'build' });
  const code = /** @type {string} */ (await plugin.load(/** @type {string} */ (plugin.resolveId('virtual:exegra-linked-specs'))));
  const linked = JSON.parse(code.replace(/^export default /, '').replace(/;\s*$/, ''));
  assert.equal(typeof linked.exegra, 'string', 'the manifest self-specification is bundled resolved');
  assert.ok(!linked.exegra.includes('"specParts"'), 'the bundled text is the assembled specification, not the manifest');
  // The shipped session builds its Project from that text and the bundled fact file (src/app/session.js, SHIPPED and SHIPPED_FACTS).
  const extracted = JSON.parse(fs.readFileSync(path.join(specsDir, 'exegra', 'extracted', 'facts.json'), 'utf8'));
  const shipped = new Project({ name: 'exegra', specText: linked.exegra, extracted });
  assert.equal(shipped.errorCount, 0);
  const cli = (/** @type {string[]} */ args) => JSON.parse(spawnSync(process.execPath, ['cli/exegra.js', ...args, '--project', 'exegra'], { cwd: root, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 }).stdout);
  const derived = cli(['derive', '--cut', 'l1']);
  assert.equal(shipped.semanticHash, derived.semanticHash, 'the shipped model has the semantic hash the command line reports');
  const d = /** @type {any} */ (deriveModel(/** @type {any} */ (shipped.model), 'l1'));
  assert.deepEqual(d.interactions.map((/** @type {any} */ i) => [i.key, i.witnesses]), derived.result.interactions.map((/** @type {any} */ i) => [i.key, i.witnesses]), 'and derives the same interactions at L1, the extracted imports included');
  assert.ok(d.interactions.some((/** @type {any} */ i) => i.kind === 'imports'));
});
