// A Playwright reporter that writes the outcome of every test with the stamp of the tree it ran on
// (tools/tree-stamp.js), to .outcomes/playwright.json. `exegra verify` reads it back (cli/outcomes.js)
// instead of running the same tests again when the stamp is still current. As for the node:test reporter,
// the stamp is taken at the start and at the end of the run, and a run that was filtered or interrupted
// is recorded as not complete.

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { treeStamp } from './tree-stamp.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const OUTPUT = path.join(repoRoot, '.outcomes', 'playwright.json');

/** @param {string} p */
const slash = (p) => p.replace(/\\/g, '/');

export default class OutcomesReporter {
  constructor() {
    /** @type {string} */
    this.treeBefore = '';
    /** @type {boolean} */
    this.filtered = false;
    /** @type {{file: string, project: string, title: string, outcome: 'pass'|'fail'|'skipped'}[]} */
    this.tests = [];
  }

  /** @param {any} config */
  onBegin(config) {
    this.treeBefore = treeStamp(repoRoot);
    this.filtered = Boolean((config.cliArgs && config.cliArgs.length) || config.cliGrep || config.cliGrepInvert || config.cliProjectFilter
      || config.cliLastFailed || config.cliOnlyChanged || config.shard || config.cliListOnly);
  }

  /** @param {any} test @param {any} result */
  onTestEnd(test, result) {
    const outcome = test.outcome();
    const state = outcome === 'skipped' || result.status === 'skipped' ? 'skipped' : outcome === 'expected' || outcome === 'flaky' ? 'pass' : 'fail';
    const tags = Array.isArray(test.tags) && test.tags.length ? ` ${test.tags.join(' ')}` : '';
    this.tests.push({
      file: slash(path.relative(repoRoot, test.location.file)),
      project: test.parent?.project?.()?.name ?? '',
      // What `playwright test -g` matches a pattern against.
      title: `${test.titlePath().join(' ')}${tags}`,
      outcome: state,
    });
  }

  /** @param {any} result */
  onEnd(result) {
    const treeAfter = treeStamp(repoRoot);
    fs.mkdirSync(path.dirname(OUTPUT), { recursive: true });
    fs.writeFileSync(OUTPUT, `${JSON.stringify({
      kind: 'playwright', finishedAt: new Date().toISOString(), treeBefore: this.treeBefore, treeAfter,
      complete: !this.filtered && (result.status === 'passed' || result.status === 'failed'), tests: this.tests,
    }, null, 1)}\n`);
  }

  printsToStdio() {
    return false;
  }
}
