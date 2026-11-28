import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseSpec } from '../../src/core/parse.js';
import { checkEditHistory } from '../../src/core/edit-history.js';
import { runCommand } from '../../cli/commands.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

const spec = readSpecFile(fileURLToPath(new URL('../../specs/exegra/spec.jsonc', import.meta.url)));
const model = parseSpec(spec).model;
const scope = { tenant: 'tenant-a', record: 'post-1' };
const attempts = ['spring','summer'].map((value,i) => ({ id: ['alice','bob'][i], ...scope, base: '7', value }));
const capture = (observations) => ({ format: 'exegra-edit-history', version: 1, complete: true, scope, base: '7', attempts, observations });
const reply = (attempt,outcome) => ({ kind:'reply',attempt,outcome });
const read = value => ({kind:'stored', ...scope, revision:'8', value});
const verify = (...obs) => checkEditHistory(model, capture(obs));

// The replay rejects a crossed reply or inconsistent stored value, accepts either valid serial order and distinguishes witnessed reply loss from incomplete capture.
// @evidence edit-history-checks-observers #
test('captured replies and durable state agree with either order only when their identities agree', () => {
  const a = reply('alice','accepted'), b = reply('bob','conflict');
  assert.deepEqual(verify(a,b,read('spring')).orders, [['alice','bob']]);
  assert.deepEqual(verify(reply('alice','conflict'),reply('bob','accepted'),read('summer')).orders, [['bob','alice']]);
  const wrong = verify(a,b,read('summer'));
  assert.equal(wrong.verdict,'incompatible');
  assert.equal(wrong.observationIndex,2);
  assert.equal(verify(a,b,{...read('spring'),revision:'7'}).verdict,'incompatible');
  assert.equal(verify(a,reply('alice','conflict'),read('spring')).observationIndex,1);
});

test('a lost response and a capture gap have different verdicts', () => {
  const lost = {kind:'reply-lost',attempt:'alice'};
  assert.equal(verify(lost,reply('bob','conflict'),read('spring')).verdict,'compatible');
  assert.equal(verify(reply('bob','conflict'),read('spring')).verdict,'inconclusive');
  assert.equal(verify(lost,reply('bob','conflict'),{...read('spring'),tenant:'tenant-b'}).verdict,'inconclusive');
  assert.equal(verify(lost,reply('alice','accepted'),read('spring')).verdict,'inconclusive');
  assert.equal(checkEditHistory(model,{...capture([]),complete:false}).verdict,'inconclusive');
});

test('the CLI replays the capture against the selected specification', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(),'edit-history-'));
  try {
    const file = path.join(dir,'capture.json');
    for (const [value, ok] of [['spring',true],['summer',false]]) {
      fs.writeFileSync(file, JSON.stringify(capture([reply('alice','accepted'),reply('bob','conflict'),read(value)])));
      const out = await runCommand('replay-edits',['--project','exegra','--file',file]);
      assert.equal(out.ok,ok);
      assert.equal(out.result.verdict,ok?'compatible':'incompatible');
    }
  } finally {
    fs.rmSync(dir,{recursive:true,force:true});
  }
});
