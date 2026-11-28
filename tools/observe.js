// Observed facts from a recorded session (WG-5696, M5). Node-only. The traffic recorder (src/app/traffic-recorder.js)
// keeps the events a running Exegra really produced as a stream of {seq, id, payload}, `id` naming an event of the
// specification; a recording is that stream as JSON (a list, or {events: [...]}). This tool counts how often each event
// occurred and writes a fact file (format exegra-observed-facts/1) that names the recording by its id, source and
// digest. The core reads it as data with provenance `observed` (src/core/extraction.js).
//
//   node tools/observe.js <recording.json> [--id <recording id>] [--out <facts file>]
//
// An observed fact says that an event occurred in that recording. It does not say it always occurs, and the absence of
// an event from a recording is "not observed", never "false".

import fs from 'node:fs';
import path from 'node:path';
import { digestOf } from './extract.js';
import { OBSERVED_FORMAT } from '../src/core/extraction.js';

/**
 * The observed facts of a recording.
 * @param {string} text the recording as JSON text @param {{id?: string, source?: string}} [opts]
 * @returns {import('../src/core/extraction.js').ObservedFacts}
 */
export function observeRecording(text, opts = {}) {
  const parsed = JSON.parse(text);
  const stream = Array.isArray(parsed) ? parsed : Array.isArray(parsed?.events) ? parsed.events : [];
  /** @type {Record<string, number>} */
  const events = {};
  let n = 0;
  for (const e of stream) {
    if (!e || typeof e.id !== 'string') continue;
    events[e.id] = (events[e.id] ?? 0) + 1;
    n++;
  }
  const digest = digestOf(text);
  const sorted = Object.fromEntries(Object.entries(events).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)));
  return { format: OBSERVED_FORMAT, provenance: 'observed', recording: { id: opts.id ?? digest.slice(7, 19), ...(opts.source ? { source: opts.source } : {}), digest, events: n }, events: sorted };
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, '$1'))) {
  const args = process.argv.slice(2);
  const arg = (/** @type {string} */ name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
  const file = args.find((a, i) => !a.startsWith('--') && (i === 0 || !args[i - 1].startsWith('--')));
  if (!file) { process.stderr.write('usage: node tools/observe.js <recording.json> [--id <id>] [--out <file>]\n'); process.exit(2); }
  const facts = observeRecording(fs.readFileSync(file, 'utf8'), { id: arg('--id'), source: path.basename(file) });
  const out = arg('--out');
  const text = `${JSON.stringify(facts, null, 1)}\n`;
  if (out) { fs.mkdirSync(path.dirname(path.resolve(out)), { recursive: true }); fs.writeFileSync(out, text); } else process.stdout.write(text);
}
