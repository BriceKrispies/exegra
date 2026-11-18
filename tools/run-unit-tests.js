// `npm test`: node --test over tests/core, two files at a time, with the spec reporter on the terminal and
// the outcomes reporter writing .outcomes/node.json (tools/outcomes-node-reporter.js) for `exegra verify`.
// Extra arguments (a file, a name pattern) are passed on; such a run is recorded as partial.

import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const extra = process.argv.slice(2);
fs.mkdirSync(path.join(repoRoot, '.outcomes'), { recursive: true });
const args = [
  '--test', '--test-concurrency=2',
  '--test-reporter=spec', '--test-reporter-destination=stdout',
  '--test-reporter=./tools/outcomes-node-reporter.js', '--test-reporter-destination=.outcomes/node.json',
  ...extra,
  ...(extra.some((a) => !a.startsWith('-')) ? [] : ['tests/core/*.test.js']),
];
const run = spawnSync(process.execPath, args, { cwd: repoRoot, stdio: 'inherit', windowsHide: true });
process.exit(run.status ?? 1);
