#!/usr/bin/env node
// Claude Code PreToolUse guard: keeps agents from reading or editing a specification file directly.
//
// A specification (specs/<project>/spec.jsonc) can be over a megabyte. Reading it costs a large share of an
// agent's budget and editing it by hand skips Exegra's checked transaction. The front door is the command line:
//   read  : node cli/exegra.js get / find / refs
//   write : node cli/exegra.js apply --dry-run, then apply
//
// Input: the hook JSON on stdin ({tool_name, tool_input, cwd?}). To refuse the script exits 2 and writes the
// reason to stderr; to allow it exits 0 silently. The decision logic is `decide`, exported for tests.
// Wired in .claude/settings.json under hooks.PreToolUse.

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { parse as parseJsonc } from 'jsonc-parser';
import { isManifest, readManifest } from './spec-manifest.js';

const REPO_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
/** Largest Read that stays allowed: the header comment of the file. */
const HEADER_LIMIT = 60;

export const REASON = [
  'Do not open or edit a specification file directly: it is large and its edits must be checked transactions.',
  'Read with:  node cli/exegra.js get --project <p> <id> [<id> ...]',
  '            node cli/exegra.js find --project <p> --kind K [--where prop=value] [--refers-to ID] [--text "..."] [--fields a,b] [--limit N]',
  '            node cli/exegra.js refs --project <p> <id>',
  'Edit with:  node cli/exegra.js apply --project <p> --file ops.json --dry-run, then the same without --dry-run.',
  '(Reading the first lines for the header comment, Read with limit <= 60, is allowed.)',
].join('\n');

/** @param {string} p */
const norm = (p) => p.replace(/\\/g, '/').toLowerCase();

/**
 * The spec files of a repository: specs/<project>/spec.jsonc and the part files of manifests among them.
 * @param {string} root absolute
 * @returns {Set<string>} normalised absolute paths
 */
export function specFiles(root) {
  /** @type {Set<string>} */
  const out = new Set();
  const specs = path.join(root, 'specs');
  /** @type {fs.Dirent[]} */
  let dirs = [];
  try { dirs = fs.readdirSync(specs, { withFileTypes: true }); } catch { return out; }
  for (const d of dirs) {
    if (!d.isDirectory()) continue;
    const file = path.join(specs, d.name, 'spec.jsonc');
    let head;
    try { head = fs.readFileSync(file, 'utf8'); } catch { continue; }
    out.add(norm(file));
    if (isManifest(head)) {
      try {
        for (const part of readManifest(head, file).parts ?? []) out.add(norm(path.resolve(path.dirname(file), part)));
      } catch {
        // Fall back to the manifest's own listing when readManifest refuses.
        const doc = parseJsonc(head);
        if (Array.isArray(doc?.specParts)) for (const part of doc.specParts) if (typeof part === 'string') out.add(norm(path.resolve(path.dirname(file), part)));
      }
    }
  }
  return out;
}

/**
 * The directories that hold part files of manifests (specs/<project>/parts, say), relative to the root. A command
 * or a search that names such a directory reaches the parts, whatever the file names.
 * @param {string} root absolute
 * @returns {string[]} normalised, relative to the root, without a trailing slash
 */
export function partDirs(root) {
  const rootNorm = norm(root).replace(/\/$/, '');
  /** @type {Set<string>} */
  const dirs = new Set();
  for (const f of specFiles(root)) {
    const dir = f.slice(0, f.lastIndexOf('/'));
    if (/\/specs\/[^/]+$/.test(dir) || !dir.startsWith(`${rootNorm}/`)) continue;
    dirs.add(dir.slice(rootNorm.length + 1));
  }
  return [...dirs];
}

/** Whether a path names a spec file. @param {string} p @param {string} cwd @param {Set<string>} files */
function isSpecPath(p, cwd, files) {
  if (typeof p !== 'string' || p === '') return false;
  const abs = norm(path.resolve(cwd, p));
  if (files.has(abs)) return true;
  return /(^|\/)specs\/[^/]+\/spec\.jsonc$/.test(abs);
}

const READERS = /(^|[\s;|&(`])(cat|type|more|less|head|tail|sed|awk|grep|egrep|fgrep|rg|ag|get-content|gc|select-string|sls|findstr|nano|vi|vim|code|notepad|cp|copy|mv|move|tee|set-content|add-content|out-file)(\s|$)/i;
const REDIRECT_INTO = />>?\s*\S*spec\.jsonc|\|\s*(tee|out-file)\b/i;

/**
 * Decide on one hook payload.
 * @param {{tool_name?: string, tool_input?: any, cwd?: string}} payload
 * @param {{root?: string}} [options]
 * @returns {{allow: true} | {allow: false, reason: string}}
 */
export function decide(payload, options = {}) {
  const root = options.root ?? REPO_ROOT;
  const cwd = payload.cwd ?? root;
  const tool = payload.tool_name ?? '';
  const input = payload.tool_input ?? {};
  const refuse = (/** @type {string} */ what) => ({ allow: /** @type {false} */ (false), reason: `${what}\n${REASON}` });
  const files = specFiles(root);
  const dirs = partDirs(root);
  const rootNorm = norm(root).replace(/\/$/, '');
  /** Whether an absolute normalised path is a part directory or inside one. */
  const inPartDir = (/** @type {string} */ abs) => dirs.some((d) => abs === `${rootNorm}/${d}` || abs.startsWith(`${rootNorm}/${d}/`));

  if (tool === 'Read') {
    const p = input.file_path ?? input.path;
    if (!isSpecPath(p, cwd, files)) return { allow: true };
    const offset = Number(input.offset ?? 0);
    const limit = input.limit === undefined ? Infinity : Number(input.limit);
    if (limit <= HEADER_LIMIT && offset <= 1) return { allow: true };
    return refuse(`Refused: Read of ${p}.`);
  }
  if (tool === 'Edit' || tool === 'Write' || tool === 'MultiEdit' || tool === 'NotebookEdit') {
    const p = input.file_path ?? input.notebook_path;
    return isSpecPath(p, cwd, files) ? refuse(`Refused: ${tool} of ${p}.`) : { allow: true };
  }
  if (tool === 'Grep') {
    // A repository-wide search is allowed (the hook cannot rewrite it); only an explicit spec target is refused.
    const targets = [input.path, input.glob].filter((x) => typeof x === 'string');
    for (const t of targets) {
      const abs = norm(path.resolve(cwd, t));
      const inSpecs = /(^|\/)specs(\/[^/]+)?\/?$/.test(abs);
      if (isSpecPath(t, cwd, files) || /spec\.jsonc|\*\.jsonc/i.test(t) || inSpecs || inPartDir(abs.replace(/\/$/, ''))) return refuse(`Refused: Grep of ${t}.`);
    }
    return { allow: true };
  }
  if (tool === 'Glob') {
    // Listing names is harmless; Glob never prints content.
    return { allow: true };
  }
  if (tool === 'Bash' || tool === 'PowerShell') {
    const cmd = typeof input.command === 'string' ? input.command : '';
    if (!/spec\.jsonc|specs[\\/]+[^\s'"]*\.jsonc/i.test(cmd) && ![...files].some((f) => norm(cmd).includes(f.split('/').slice(-3).join('/'))) && !dirs.some((d) => norm(cmd).includes(d))) return { allow: true };
    // The programmatic path stays open: the CLI and scripts that parse with jsonc-parser.
    if (/cli[\\/]exegra\.js|jsonc-parser/i.test(cmd)) return { allow: true };
    if (READERS.test(cmd) || REDIRECT_INTO.test(cmd)) return refuse('Refused: this shell command reads or edits a specification file.');
    return { allow: true };
  }
  return { allow: true };
}

async function main() {
  let raw = '';
  for await (const chunk of process.stdin) raw += chunk;
  /** @type {any} */
  let payload;
  try { payload = JSON.parse(raw); } catch { return; }
  const verdict = decide(payload);
  if (!verdict.allow) {
    process.stderr.write(`${verdict.reason}\n`);
    process.exitCode = 2;
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) await main();
