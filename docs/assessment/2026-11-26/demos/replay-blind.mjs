// Demonstration: the live replay (src/core/replay.js) reports no divergence for a recorded stream in which the
// implementation drops the content of a write and its result hash, and in which an external event arrives that
// the model does not accept in its current state.
import { replayStream } from '../../../../src/core/replay.js';
const ents = [];
const add = (kind, id, data, owner) => { const e = { kind, id, data, owner }; ents.push(e); return e; };
for (const id of ['open', 'save-requested', 'write-intent', 'saved', 'close']) add('event', id, {});
add('behavior', 'client', { subject: 'c', initial: 'idle', variables: [{ name: 'baseHash', initial: 'h0' }] });
add('behavior', 'server', { subject: 's', initial: 'up', variables: [] });
for (const s of ['idle', 'ready', 'saving']) add('state', s, {}, 'client');
add('state', 'up', {}, 'server');
add('transition', 'c-open', { from: 'idle', to: 'ready', on: 'open', effects: [] }, 'client');
add('transition', 'c-save', { from: 'ready', to: 'saving', on: 'save-requested', effects: [{ emit: 'write-intent', payload: { file: 'event.file', text: 'event.text', base: 'baseHash' } }] }, 'client');
add('transition', 'c-saved', { from: 'saving', to: 'ready', on: 'saved', effects: [] }, 'client');
add('transition', 'c-close', { from: 'ready', to: 'idle', on: 'close', effects: [] }, 'client');
add('transition', 's-write', { from: 'up', to: 'up', on: 'write-intent', effects: [{ emit: 'saved', payload: { file: 'event.file' } }] }, 'server');
add('scenario', 'live-session', { behaviors: ['client', 'server'], steps: [] });
const byKind = {}; for (const e of ents) (byKind[e.kind] ??= []).push(e);
const model = { entities: new Map(ents.map((e) => [e.id, e])), byKind, meta: {} };
const stream = [
  { seq: 1, id: 'open', payload: {} },
  { seq: 2, id: 'save-requested', payload: { file: 'spec', text: 'abc' } },
  { seq: 3, id: 'write-intent', payload: { file: 'spec', base: 'some-other-hash' } },   // no text sent at all; a base hash the model never had
  { seq: 4, id: 'saved', payload: { file: 'spec' } },          // and reports no hash
  { seq: 5, id: 'close', payload: {} },
  { seq: 6, id: 'save-requested', payload: { file: 'spec', text: 'lost' } }, // a save after close: model idle accepts nothing
];
const r = replayStream(model, stream);
console.log('divergences:', JSON.stringify(r.divergences ?? r));
