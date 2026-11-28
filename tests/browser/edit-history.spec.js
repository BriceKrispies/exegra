import { test, expect } from '@playwright/test';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { parse } from 'jsonc-parser';
import { SCRATCH, ROOT, resetScratch, readScratch } from './scratch.js';

const hash = (s) => createHash('sha256').update(s).digest('hex');
const workspaceName = text => parse(text).components.find(c => c.id === 'workspace-service').name;

for (const [winner, cross] of [[0,false],[1,false],[0,true]]) {
  test(`two editing sessions from one hash with editor ${winner + 1} first and ${cross ? 'crossed' : 'normal'} replies`, { tag: '@full' }, async ({ browser, baseURL }, info) => {
    test.setTimeout(120_000);
    resetScratch('exegra');
    const pages = await Promise.all([browser.newPage(), browser.newPage()]);
    const routes = pages.map(() => Promise.withResolvers());
    const responses = pages.map(() => Promise.withResolvers());
    const names = ['Workspace writer Alice','Workspace writer Bob'];
    const scope = {tenant:SCRATCH.exegra,record:'spec.jsonc'};
    const base = hash(readScratch('exegra','spec.jsonc'));
    try {
      await Promise.all(pages.map(async (page, i) => {
        await page.goto(`${baseURL}/?project=${SCRATCH.exegra}`);
        await page.waitForFunction(name => window.__exegra?.session.projectName === name && window.__exegra?.session.model, SCRATCH.exegra);
        await page.evaluate(() => window.__exegra.session.select('workspace-service'));
        // Each page owns its own observer. Both submissions are held before either reaches the server.
        await page.route('**/__exegra/write', route => { routes[i].resolve(route); });
        page.on('response', res => {
          if (new URL(res.url()).pathname === '/__exegra/write') responses[i].resolve(res.status());
        });
        const editor = page.getByTestId('inspector').locator('[data-prop="name"] input');
        await editor.fill(names[i]);
        await editor.press('Enter');
      }));
      const held = await Promise.all(routes.map(r => r.promise));
      const attempts = held.map((route,i) => {
        const body = route.request().postDataJSON();
        expect(body.baseHash).toBe(base);
        expect(body.name).toBe(scope.tenant);
        expect(body.file).toBe('spec');
        expect(workspaceName(body.text)).toBe(names[i]);
        return {id:['alice','bob'][i],...scope,base:body.baseHash,value:hash(body.text)};
      });
      // Actually perform both writes in the selected order. The negative control crosses the
      // server's two real HTTP replies at the browser boundary before either UI sees one.
      const actual = [];
      for (const i of [winner,1-winner]) actual[i] = await held[i].fetch();
      for (const i of [0,1]) await held[i].fulfill({response:actual[cross ? 1-i : i]});
      const statuses = await Promise.all(responses.map(r => r.promise));
      const observations = statuses.map((status,i) => {
        expect([200,409]).toContain(status);
        return {kind:'reply',attempt:attempts[i].id,outcome:status===200?'accepted':'conflict'};
      });
      const durable = readScratch('exegra','spec.jsonc');
      observations.push({kind:'stored',...scope,value:hash(durable),revision:hash(durable)});
      const capture = {format:'exegra-edit-history',version:1,complete:true,scope,base,attempts,observations};
      const file = info.outputPath('capture.json');
      fs.writeFileSync(file, JSON.stringify(capture,null,2));
      const replay = spawnSync(process.execPath,['cli/exegra.js','replay-edits','--file',file],{cwd:ROOT,encoding:'utf8'});
      expect(replay.status,replay.stderr).toBe(cross ? 1 : 0);
      const result = JSON.parse(replay.stdout).result;
      expect(result.verdict).toBe(cross ? 'incompatible' : 'compatible');
      expect(workspaceName(durable)).toBe(names[winner]);
      const conflict = pages[statuses.indexOf(409)];
      await expect(conflict.getByTestId('save-state')).toContainText(/conflict/i);
      await info.attach('capture.json',{body:JSON.stringify(capture,null,2),contentType:'application/json'});
      if (!cross && winner===0) {
        await conflict.screenshot({path:path.join(ROOT,'screenshots','two-session-edit-conflict.png')});
      }
    } finally {
      await Promise.all(pages.map(page => page.close()));
    }
  });
}
