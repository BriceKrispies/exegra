import { test } from 'node:test';
import assert from 'node:assert/strict';
import { pairHistoryWithLog } from '../../src/ui/activity.js';

/** A session of `commits` commits, each logging one 'change' entry with the commit's revision. */
function session(commits, { logCap = 400 } = {}) {
  const history = [];
  const all = [];
  let seq = 0;
  for (let rev = 2; rev < commits + 2; rev++) {
    history.push({ revision: rev, label: `commit ${rev}` });
    all.push({ seq: ++seq, kind: 'change', message: `commit ${rev}`, detail: { revision: rev } });
    if (rev % 3 === 0) all.push({ seq: ++seq, kind: 'error', message: 'noise' });
  }
  const log = all.length > logCap ? all.slice(all.length - logCap) : all;
  return { history, log };
}

test('pairs each history entry with its own log entry after the log cap has dropped older ones', () => {
  const { history, log } = session(450);
  assert.equal(history.length, 450);
  assert.ok(log.filter((l) => l.kind === 'change').length < 450, 'the log is capped, history is not');
  const pairs = pairHistoryWithLog(history, log);
  assert.equal(pairs.length, 450);
  for (const { entry, key } of pairs) {
    const logged = log.find((l) => l.kind === 'change' && l.detail.revision === entry.revision);
    if (logged) assert.equal(key, logged.seq, `revision ${entry.revision} pairs with its own log entry`);
    else assert.equal(key, null, `revision ${entry.revision} lost its log entry and is unpaired`);
  }
});

test('with more than 400 commits, the newest 400 entries keep the right keys', () => {
  const { history, log } = session(430);
  const pairs = pairHistoryWithLog(history, log);
  const newest = pairs.slice(-100);
  for (const { entry, key } of newest) {
    const logged = log.find((l) => l.kind === 'change' && l.detail.revision === entry.revision);
    assert.ok(logged, `revision ${entry.revision} is still logged`);
    assert.equal(key, logged.seq);
  }
  assert.equal(pairs[0].key, null, 'the oldest commit has no log entry');
});

test('an unlogged change in the log does not shift later pairings', () => {
  const history = [{ revision: 5 }, { revision: 6 }];
  const log = [
    { seq: 1, kind: 'info', message: 'opened' },
    { seq: 2, kind: 'change', message: 'rev 6', detail: { revision: 6 } },
  ];
  const pairs = pairHistoryWithLog(history, log);
  assert.deepEqual(pairs.map((p) => p.key), [null, 2]);
});
