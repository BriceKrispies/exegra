// Demonstration: checkRefinementTrace (src/core/refinement.js) accepts an implementation that silently
// ignores an event its model must react to. Fixture = the lease of tests/core/refinement.test.js.
import { checkRefinementTrace } from '../../../../src/core/refinement.js';
const ent = (kind, id, data, owner) => ({ kind, id, data, owner });
const A = ent('behavior', 'lease-model', { initial: 'lm-free', variables: [{ name: 'holder', initial: '' }, { name: 'epoch', initial: 0 }] });
const I = ent('behavior', 'lease-impl', { level: 'implementation', initial: 'li-free',
  variables: [{ name: 'owner', initial: '' }, { name: 'gen', initial: 0 }, { name: 'renewals', initial: 0 }],
  refines: 'lease-model',
  refinement: { states: { 'li-free': 'lm-free', 'li-held': 'lm-held', 'li-renewing': 'lm-held' },
    variables: { holder: 'owner', epoch: 'gen' },
    transitions: { 'li-acquire': 'lm-acquire', 'li-renew': null, 'li-renewed': null, 'li-release': 'lm-release' } } });
const T = [
  ent('transition', 'lm-acquire', { from: 'lm-free', to: 'lm-held', on: 'acquire', guard: "holder == ''", effects: [{ set: 'holder', to: 'event.client' }, { set: 'epoch', to: 'epoch + 1' }, { emit: 'granted', payload: { client: 'event.client' } }] }, 'lease-model'),
  ent('transition', 'lm-release', { from: 'lm-held', to: 'lm-free', on: 'release', guard: 'event.client == holder', effects: [{ set: 'holder', to: "''" }] }, 'lease-model'),
  ent('transition', 'li-acquire', { from: 'li-free', to: 'li-held', on: 'acquire', effects: [{ set: 'owner', to: 'event.client' }, { set: 'gen', to: 'gen + 1' }, { emit: 'granted', payload: { client: 'event.client', gen: 'gen' } }] }, 'lease-impl'),
  ent('transition', 'li-renew', { from: 'li-held', to: 'li-renewing', on: 'renew', effects: [{ set: 'renewals', to: 'renewals + 1' }] }, 'lease-impl'),
  ent('transition', 'li-renewed', { from: 'li-renewing', to: 'li-held', on: 'renewed', effects: [] }, 'lease-impl'),
  ent('transition', 'li-release', { from: 'li-held', to: 'li-free', on: 'release', effects: [{ set: 'owner', to: "''" }] }, 'lease-impl'),
];
const all = [A, I, ...T];
const model = { entities: new Map(all.map((e) => [e.id, e])), byKind: { behavior: [A, I], transition: T } };
const m = (state, owner, gen, renewals) => ({ machines: { 'lease-impl': { state, vars: { owner, gen, renewals } } } });
// The engine's trace for scenario: acquire(a)@0, renew@1, release(a)@2 [ignored in li-renewing], renewed@3, acquire(b)@4 [ignored in li-held]
const trace = { initial: m('li-free', '', 0, 0), steps: [
  { index: 0, time: 0, event: { id: 'acquire', payload: { client: 'a' } }, fired: [{ behavior: 'lease-impl', transition: 'li-acquire', from: 'li-free', to: 'li-held', emitted: [{ event: 'granted', time: 0, payload: { client: 'a', gen: 1 } }] }], config: m('li-held', 'a', 1, 0) },
  { index: 1, time: 1, event: { id: 'renew', payload: {} }, fired: [{ behavior: 'lease-impl', transition: 'li-renew', from: 'li-held', to: 'li-renewing', emitted: [] }], config: m('li-renewing', 'a', 1, 1) },
  { index: 2, time: 2, event: { id: 'release', payload: { client: 'a' } }, fired: [], config: m('li-renewing', 'a', 1, 1) },
  { index: 3, time: 3, event: { id: 'renewed', payload: {} }, fired: [{ behavior: 'lease-impl', transition: 'li-renewed', from: 'li-renewing', to: 'li-held', emitted: [] }], config: m('li-held', 'a', 1, 1) },
  { index: 4, time: 4, event: { id: 'acquire', payload: { client: 'b' } }, fired: [], config: m('li-held', 'a', 1, 1) },
] };
const r = checkRefinementTrace(model, I, trace, 'release-during-renew');
console.log(JSON.stringify({ failure: r.failure, unsupported: r.unsupported, checkedSteps: r.checkedSteps, movingSteps: r.movingSteps }));
console.log('Model on the same inputs: acquire(a)->held/granted a; release(a)->free; acquire(b)->held/granted b. Impl: b never granted, a holds forever.');
