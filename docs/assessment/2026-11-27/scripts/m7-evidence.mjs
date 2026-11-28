// Generate-evaluate-accept on the three external fixtures (WG-5735, M7): for each of the compiler, the distributed
// application and the event-driven system, generate candidates from the established semantics, read the ones a person
// gave, evaluate them (V1 to V7, measurements, evidence), accept one through a transaction on an in-memory project, undo it,
// accept it again, and run the multiscale commands on the accepted specification. Writes, under
// docs/assessment/2026-11-27/m7/:
//
//   <fixture>-candidates.json   every candidate's report, the comparison rows and the purity check (hash before and after)
//   <fixture>-accept.json       the operations of the accepted candidate's transaction and what holds after it
//   <fixture>.md                the same as a report
//
//   node docs/assessment/2026-11-27/scripts/m7-evidence.mjs [--only compiler,distributed,event-driven]
//
// The reports hold no score and no ranking: the measurements are side by side, in the order the candidates are listed.
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../../../src/core/analyze.js';
import { Project } from '../../../../src/core/project.js';
import { initEngine } from '../../../../src/core/engine.js';
import { stableStringify } from '../../../../src/core/stable-json.js';
import { semanticHash } from '../../../../src/core/hash.js';
import { baseFacts } from '../../../../src/core/abstraction.js';
import { compareCandidates, generateCandidates, candidatesOfData, acceptCandidate, NOT_MEANING } from '../../../../src/core/decomposition.js';
import { runCommand } from '../../../../cli/commands.js';

initEngine();
const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../../../..');
const OUT = path.join(ROOT, 'docs/assessment/2026-11-27/m7');
const FIX = path.join(ROOT, 'tests/fixtures/multiscale-external');
fs.mkdirSync(OUT, { recursive: true });
const only = process.argv.includes('--only') ? process.argv[process.argv.indexOf('--only') + 1].split(',') : null;

/** What each fixture exercises of the multiscale audit, and the claim it states at a cut. */
const FIXTURES = [
  {
    name: 'compiler', scope: 'compiler', accept: 'compiler-pipeline-thirds', claim: { from: 'emission', to: 'syntax', kinds: ['data-flow', 'invokes'], text: 'At the accepted cut no data flows back from emission to syntax.' }, post: ['compose-functions'],
    audit: 'Section 6.1',
    requirements: [
      'Lifting along a pipeline: the data-flow facts between stages lift to the blocks of every candidate with their witnesses (V2).',
      'Shared parts: the diagnostics sink is a block of its own in every candidate, with fan-in from the stages; it is not folded into a stage.',
      'Functional composition (WG-5730): the functions attached to elements still compose after the accepted hierarchy is recorded (compose-functions is unchanged by it).',
      'Overlap and coverage (V1) on a pipeline whose stages a person regroups.',
    ],
  },
  {
    name: 'distributed', scope: 'shop', accept: 'shop-by-tier', claim: { from: 'back-office', to: 'presentation', kinds: ['invokes'], text: 'At the accepted cut the back office never invokes the presentation tier.' }, post: ['lift-faults'],
    audit: 'Section 6.2',
    requirements: [
      'Several named hierarchies over the same elements: the logical hierarchy and the deployment hierarchy; the accepted hierarchy is a third.',
      'Realisation maps (WG-5730): each logical invocation is realised by a path of network links; the maps are checked again at the accepted cut and stay intact.',
      'Fault lifting through realisation: the failure modes of the deployment level lift to the logical interactions they fail, at the accepted cut.',
      'Delivery guarantees and contracts carried on lifted interactions (the summaries of the derived model).',
    ],
  },
  {
    name: 'event-driven', scope: 'telemetry-platform', accept: 'telemetry-by-role', claim: { from: 'consumers', to: 'producers', kinds: ['invokes', 'notifies', 'publishes', 'subscribes', 'reads'], text: 'At the accepted cut no dependency path leads from the consumers to the producers.' }, post: ['coherence', 'boundary-contracts'],
    audit: 'Section 6.3',
    requirements: [
      'Connectors as first-class elements and path contraction (publishes then subscribes through a declared connector gives notifies, naming the connector): the contractions of the accepted cut.',
      'V5 over connector-mediated messages: a message that travels through a topic is witnessed by its two relationships lifting at the cut.',
      'V6 where a block carries declared abstract behaviour (processing-flow abstracts the aggregator and the rules): a refinement check at the block, and not applicable where no block does.',
      'V7: the rule-check contract is typed by its events; reading-feed is not, so a candidate that separates the gateway from the filter is rejected.',
      'Hiding: rule-req and rule-res are internal to processing and hidden at its abstraction.',
    ],
  },
].filter((f) => !only || only.includes(f.name));

const cli = async (cmd, args) => { const r = await runCommand(cmd, args); return r; };
const pick = (/** @type {any} */ r) => (r.ok ? r.result : { error: r.error });

for (const fx of FIXTURES) {
  const file = path.join(FIX, `${fx.name}.jsonc`);
  const text = fs.readFileSync(file, 'utf8');
  const model = /** @type {any} */ (analyzeSpec(text).model);
  const given = candidatesOfData(JSON.parse(fs.readFileSync(path.join(FIX, `${fx.name}-candidates.json`), 'utf8')));
  const common = { scope: fx.scope, grain: /** @type {const} */ ('leaves') };
  const hashBefore = semanticHash(model);
  const factsBefore = stableStringify(baseFacts(model).facts);
  const generated = generateCandidates(model, { ...common, bases: given.map((c) => ({ ...common, ...c })) });
  const all = [...given.map((c) => ({ ...common, ...c })), ...generated.candidates];
  const cmp = compareCandidates(model, all, { ...common, evidence: true });
  const again = compareCandidates(model, all, { ...common, evidence: true });
  const pure = { hashBefore, hashAfter: semanticHash(model), factsUnchanged: stableStringify(baseFacts(model).facts) === factsBefore, repeatedIdentical: stableStringify(cmp) === stableStringify(again) };
  fs.writeFileSync(path.join(OUT, `${fx.name}-candidates.json`), `${JSON.stringify({ fixture: `tests/fixtures/multiscale-external/${fx.name}.jsonc`, ...common, purity: pure, skipped: generated.skipped, comparison: { candidates: cmp.candidates, rows: cmp.rows }, candidates: cmp.reports.map((r) => ({ ...r, acceptance: undefined })), note: NOT_MEANING }, null, 1)}\n`);

  // Accept one through a transaction, undo it, accept it again.
  const project = new Project({ specText: text, name: fx.name });
  const chosen = all.find((c) => c.id === fx.accept);
  const h0 = project.semanticHash;
  const dry = acceptCandidate(project, chosen, { ...common, dryRun: true });
  const accepted = acceptCandidate(project, chosen, { ...common, label: `Accept decomposition ${fx.accept}` });
  if (!accepted.ok) throw new Error(`${fx.name}: ${accepted.message}`);
  const h1 = project.semanticHash;
  project.undo();
  const hUndone = project.semanticHash;
  project.redo();
  const hRedone = project.semanticHash;
  // A claim stated at the accepted cut: a level-bound structural claim, added by a second transaction.
  const claimOp = { type: 'AddClaim', data: { id: `${fx.accept}-level-claim`, kind: 'structural', statement: fx.claim.text, subjects: [fx.claim.from, fx.claim.to], evaluate: { method: 'no-relationship', cut: `${fx.accept}-cut`, from: fx.claim.from, to: fx.claim.to, kinds: fx.claim.kinds } } };
  const claimTx = project.apply([claimOp], { label: `Claim at the cut of ${fx.accept}` });
  if (!claimTx.ok) throw new Error(`${fx.name}: ${claimTx.message}`);
  const acceptedText = project.specText;
  const tmp = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'm7-')), `${fx.name}-accepted.jsonc`);
  fs.writeFileSync(tmp, acceptedText);
  const hid = fx.accept, cut = `${hid}-cut`, top = `${hid}-top`;
  const spec = ['--spec', tmp];
  const validate = pick(await cli('validate', spec));
  const derived = pick(await cli('derive', [...spec, '--cut', cut]));
  const nav = pick(await cli('cut', [...spec, '--cut', cut]));
  const evaluated = {};
  for (const claim of [`${fx.accept}-level-claim`]) {
    for (const c of [cut, top]) { const r = pick(await cli('evaluate', [claim, ...spec, '--cut', c])); evaluated[`${claim}@${c}`] = r.results ? { status: r.results[0].status, expressible: !(r.results[0].diagnostics ?? []).some((/** @type {any} */ d) => d.code === 'claim.not-expressible') } : r; }
  }
  const post = {};
  for (const cmd of fx.post) post[cmd] = pick(await cli(cmd, cmd === 'lift-faults' ? [...spec, '--cut', cut] : [...spec]));
  const summary = {
    emptied: /** @type {any} */ (accepted.report.acceptance).emptied,
    fixture: fx.name, accepted: fx.accept, dryRunOperations: dry.operations.length, operations: accepted.operations.length,
    semanticHash: { before: h0, afterAccept: h1, afterUndo: hUndone, afterRedo: hRedone, undoRestores: hUndone === h0, redoRestores: hRedone === h1 },
    validate: { errors: validate.errors, warnings: validate.warnings },
    cut: { id: cut, blocks: derived.blocks?.length, interactions: derived.interactions?.length, connectors: derived.connectors?.length, realisations: derived.realisations === undefined ? undefined : { maps: derived.realisations.length, ok: derived.realisations.every((/** @type {any} */ r) => r.ok !== false) }, diagnostics: (derived.diagnostics ?? []).map((/** @type {any} */ d) => `${d.condition}:${d.code}`) },
    navigation: { hierarchy: hid, cuts: [top, cut], blocksAtCut: nav.blocks?.map((/** @type {any} */ b) => b.id) },
    levelBoundClaims: evaluated,
    after: Object.fromEntries(Object.entries(post).map(([k, v]) => [k, summariseAfter(k, v)])),
  };
  fs.writeFileSync(path.join(OUT, `${fx.name}-accept.json`), `${JSON.stringify({ ...summary, operationList: accepted.operations, claimOperation: claimOp }, null, 1)}\n`);
  fs.writeFileSync(path.join(OUT, `${fx.name}.md`), reportOf(fx, cmp, generated, pure, summary));
  console.log(`${fx.name}: ${cmp.reports.length} candidates, accepted ${fx.accept}, undo restores ${summary.semanticHash.undoRestores}`);
}

/** @param {string} cmd @param {any} v */
function summariseAfter(cmd, v) {
  if (cmd === 'compose-functions') return { composites: (v.composites ?? v.functions ?? []).length, diagnostics: (v.diagnostics ?? []).length };
  if (cmd === 'lift-faults') return { modes: (v.modes ?? v.failureModes ?? []).length, keys: Object.keys(v) };
  if (cmd === 'coherence') return { ok: v.ok, messages: v.messages, unwitnessed: (v.unwitnessed ?? []).length };
  if (cmd === 'boundary-contracts') return { ok: v.ok, hops: v.hops, findings: (v.findings ?? []).map((/** @type {any} */ f) => f.relationship) };
  return {};
}

/** @param {any} fx @param {any} cmp @param {any} generated @param {any} pure @param {any} s */
function reportOf(fx, cmp, generated, pure, s) {
  const fmt = (/** @type {any} */ v) => (v === null || v === undefined ? '-' : String(v));
  const ids = cmp.candidates;
  const L = [];
  L.push(`# M7 report: ${fx.name}`, '', `Generated by \`docs/assessment/2026-11-27/scripts/m7-evidence.mjs\` from \`tests/fixtures/multiscale-external/${fx.name}.jsonc\` (${fx.audit} of the multiscale audit). Scope \`${fx.scope}\`, grain leaves. ${NOT_MEANING}`, '');
  L.push('## Purity', '', `Fact base before and after evaluating ${ids.length} candidates twice: hash \`${pure.hashBefore}\` and \`${pure.hashAfter}\`; facts unchanged: ${pure.factsUnchanged}; the repeated evaluation is byte-identical: ${pure.repeatedIdentical}.`, '');
  L.push('## Candidates and validity', '', '| Candidate | Source | Status | V1 | V2 | V3 | V4 | V5 | V6 | V7 |', '|---|---|---|---|---|---|---|---|---|---|');
  for (const r of cmp.reports) L.push(`| ${r.id} | ${r.source} | ${r.status} | ${['V1', 'V2', 'V3', 'V4', 'V5', 'V6', 'V7'].map((id) => fmt(r.conditions.find((/** @type {any} */ c) => c.id === id)?.status)).join(' | ')} |`);
  L.push('', 'Failures, with their witnesses:', '');
  let any = false;
  for (const r of cmp.reports) for (const c of r.conditions) for (const f of c.failures) { any = true; L.push(`- \`${r.id}\` ${c.id} \`${f.code}\`: witnesses ${f.witnesses.slice(0, 8).map((/** @type {string} */ w) => `\`${w}\``).join(', ')}${f.witnesses.length > 8 ? ', ...' : ''}`); }
  if (!any) L.push('- none');
  L.push('', 'Conditions that do not apply, with the reason:', '');
  const reasons = new Set();
  for (const r of cmp.reports) for (const c of r.conditions) if (c.status === 'not-applicable') reasons.add(`${c.id}: ${c.reason}`);
  for (const x of reasons) L.push(`- ${x}`);
  if (!reasons.size) L.push('- none');
  L.push('', '## Measurements, side by side', '', `| Measure | ${ids.join(' | ')} |`, `|---|${ids.map(() => '---').join('|')}|`);
  for (const row of cmp.rows) if (row.id !== 'status') L.push(`| ${row.label} | ${ids.map((/** @type {string} */ id) => fmt(row.values[id])).join(' | ')} |`);
  if (generated.skipped.length) { L.push('', 'Sources that generated nothing:', ''); for (const x of generated.skipped) L.push(`- ${x.source}: ${x.reason}`); }
  L.push('', '## Acceptance', '', `Accepted \`${s.accepted}\` through one transaction of ${s.operations} operations (\`${fx.name}-accept.json\` lists them). It records the hierarchy \`${s.navigation.hierarchy}\` and the cuts ${s.navigation.cuts.map((/** @type {string} */ c) => `\`${c}\``).join(', ')}.`, '');
  L.push(`- Semantic hash before \`${s.semanticHash.before}\`, after \`${s.semanticHash.afterAccept}\`; undo restores the first (${s.semanticHash.undoRestores}); redo restores the second (${s.semanticHash.redoRestores}).`);
  L.push(`- Elements the candidate emptied (their members sit in blocks now; they stay as empty blocks of the cut): ${s.emptied.length ? s.emptied.map((/** @type {string} */ e) => `\`${e}\``).join(', ') : 'none'}.`);
  L.push(`- The accepted specification validates with ${s.validate.errors} errors and ${s.validate.warnings} warnings.`);
  L.push(`- At \`${s.cut.id}\`: ${s.cut.blocks} blocks, ${s.cut.interactions} derived interactions${s.cut.connectors !== undefined ? `, ${s.cut.connectors} connector contractions` : ''}; abstraction diagnostics: ${s.cut.diagnostics.length ? s.cut.diagnostics.join(', ') : 'none'}.`);
  for (const [k, v] of Object.entries(s.levelBoundClaims)) L.push(`- Level-bound claim \`${k}\`: ${JSON.stringify(v)}.`);
  for (const [k, v] of Object.entries(s.after)) L.push(`- \`${k}\` on the accepted specification: ${JSON.stringify(v)}.`);
  L.push('', '## Multiscale requirements this run exercised', '');
  for (const r of fx.requirements) L.push(`- ${r}`);
  L.push('');
  return L.join('\n');
}
