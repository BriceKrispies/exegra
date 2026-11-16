#!/usr/bin/env node
// Agent command line for Exegra. Parses argv, runs one command from cli/commands.js,
// prints exactly one JSON document on stdout and sets the exit code.
//
//   node cli/exegra.js <command> [args] [--project <name>] [--specs <dir>] [--pretty]
//
// Exit codes: 0 ok, 1 command failed (ok false), 2 usage error.
// Human-oriented progress notes go to stderr; stdout is the JSON document only.

import { runCommand, exitCodeOf } from './commands.js';

const argv = process.argv.slice(2);
const pretty = argv.includes('--pretty');
const tokens = argv.filter((t) => t !== '--pretty');
const first = tokens[0];

/** @param {string} message */
const noCommandEnvelope = (message) => ({
  ok: false,
  command: null,
  project: null,
  error: { code: 'usage.missing-argument', message },
  diagnostics: [],
});

/** @type {Record<string, any>} */
let envelope;
if (first === undefined) {
  envelope = noCommandEnvelope('Give a command. Run "exegra help" for the list.');
} else if (first === '-h' || first === '--help') {
  envelope = await runCommand('help', [], {});
} else if (first.startsWith('-')) {
  envelope = noCommandEnvelope(`Expected a command before "${first}". Run "exegra help" for the list.`);
} else {
  envelope = await runCommand(first, tokens.slice(1), {
    log: (message) => process.stderr.write(`${message}\n`),
  });
}

process.stdout.write(`${JSON.stringify(envelope, null, pretty ? 2 : 0)}\n`);
process.exitCode = exitCodeOf(/** @type {any} */ (envelope));
