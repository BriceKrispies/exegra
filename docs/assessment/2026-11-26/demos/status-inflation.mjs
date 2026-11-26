// Status inflation through src/core/claims.js with a hand-built model (the Lean-derived model is
// unavailable here; evaluateClaims reads only model.entities, byKind, meta and semanticHash).
import { evaluateClaims } from '../../../../src/core/claims.js';
const ent = (kind, id, data) => ({ kind, id, data });
const claims = [
  ent('claim', 'pages-like', { kind: 'structural', statement: 'Every push to main publishes the production build.', evaluate: { method: 'external-evidence' } }),
  ent('claim', 'p-equals-np', { kind: 'structural', statement: 'P = NP.', evaluate: { method: 'external-evidence' } }),
  ent('claim', 'doc-only', { kind: 'measured', statement: 'p99 ack latency < 50 ms in production.', evaluate: { method: 'external-evidence' } }),
  ent('claim', 'half-tested', { kind: 'invariant', statement: 'A and B both hold.', evaluate: { method: 'external-evidence' } }),
  ent('claim', 'lean-no-about', { kind: 'invariant', statement: 'The simulator never loses a message.', evaluate: { method: 'lean-theorem', theorem: 'Nat.add_comm' } }),
  ent('claim', 'lean-stale', { kind: 'invariant', statement: 'runInput terminates.', evaluate: { method: 'lean-theorem', theorem: 'Exegra.runInput_terminates', about: ['Exegra.runInput'] } }),
];
const evidence = [
  ent('evidence', 'ev-yaml-regex', { claim: 'pages-like', kind: 'test', ref: 'tests/core/pages-site.test.js#the Pages workflow runs on every push to main' }),
  ent('evidence', 'ev-unrelated', { claim: 'p-equals-np', kind: 'test', ref: 'tests/core/expr.test.js' }),
  ent('evidence', 'ev-doc', { claim: 'doc-only', kind: 'document', ref: 'illustrative://no-such-report' }),
  ent('evidence', 'ev-a', { claim: 'half-tested', kind: 'test', ref: 'tests/a.test.js' }),
  ent('evidence', 'ev-b', { claim: 'half-tested', kind: 'test', ref: 'tests/b.test.js' }),
];
const all = [...claims, ...evidence];
const model = { semanticHash: 'demo', entities: new Map(all.map((e) => [e.id, e])), byKind: { claim: claims, evidence }, meta: { verificationMethods: {} } };
const facts = { found: true, kind: 'theorem', kernel: 'ok', axioms: ['propext'], lean: '4.x', checkedAt: '2026-11-25T15:21:09Z' };
const recorded = {
  results: { 'ev-yaml-regex': { outcome: 'pass' }, 'ev-unrelated': { outcome: 'pass' }, 'ev-a': { outcome: 'pass' } /* ev-b: never run */ },
  theorems: { 'Nat.add_comm': { ...facts }, 'Exegra.runInput_terminates': { ...facts, about: { 'Exegra.runInput': { kind: 'definition', inStatement: true } } } },
};
for (const r of evaluateClaims(model, { recorded })) console.log(`${r.claimId.padEnd(14)} ${r.status.padEnd(10)} ${r.explanation.slice(0, 150)}`);
