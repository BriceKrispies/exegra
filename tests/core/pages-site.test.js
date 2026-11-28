// The GitHub Pages site (.github/workflows/pages.yml, vite.config.js), as far as the files establish it: the
// workflow is triggered by a push to main with no filter that could skip one, and in one job with no condition
// and no ignored failure it builds the Lean core, validates Exegra's own specification, builds the bundle and
// uploads dist, in that order; a deploy job that needs that job deploys it, and only on main. The bundle's asset
// URLs are relative, so it loads under the repository's sub-path.
//
// What this does not establish: that GitHub runs the workflow at all (Pages enabled, the workflow enabled, a
// [skip ci] push), or that every push is published (a queued run is replaced by a newer push under the
// workflow's concurrency group). The checks are structural; they are shown to fail on the five mutants of
// docs/assessment/2026-11-26/demos/pages-mutants.mjs, not on every edit that breaks publishing.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const workflowText = fs.readFileSync(path.join(repoRoot, '.github', 'workflows', 'pages.yml'), 'utf8');

/**
 * A reader for the YAML subset GitHub workflows use here: block mappings and sequences by indentation, a mapping
 * started on a sequence item's line, block scalars (| and >), flow sequences ([a, b]), quoted and plain scalars,
 * and comments. Enough to read the structure of pages.yml; it refuses what it does not understand.
 * @param {string} text
 * @returns {any}
 */
export function readWorkflow(text) {
  const raw = text.split(/\r?\n/);
  /** @param {string} s */
  const stripComment = (s) => {
    let quote = '';
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (quote) { if (c === quote) quote = ''; continue; }
      if (c === '"' || c === "'") quote = c;
      else if (c === '#' && (i === 0 || /\s/.test(s[i - 1]))) return s.slice(0, i).replace(/\s+$/, '');
    }
    return s.replace(/\s+$/, '');
  };
  /** @type {{indent: number, text: string, line: number}[]} */
  const lines = [];
  for (let i = 0; i < raw.length; i++) {
    const t = stripComment(raw[i]);
    if (t.trim() === '') continue;
    lines.push({ indent: t.length - t.trimStart().length, text: t.trim(), line: i });
  }
  let pos = 0;
  /** @param {string} s @returns {any} */
  const scalar = (s) => {
    if (/^'.*'$/.test(s)) return s.slice(1, -1).replace(/''/g, "'");
    if (/^".*"$/.test(s)) return JSON.parse(s);
    if (/^\[.*\]$/.test(s)) return s.slice(1, -1).split(',').map((x) => x.trim()).filter((x) => x !== '').map(scalar);
    if (s === 'true') return true;
    if (s === 'false') return false;
    if (/^-?\d+(\.\d+)?$/.test(s)) return Number(s);
    return s;
  };
  /** The raw lines of a block scalar after `lines[pos - 1]`, deeper than `indent`. @param {number} indent @param {string} style */
  const blockScalar = (indent, style) => {
    const start = lines[pos - 1].line + 1;
    const body = [];
    let end = start;
    for (let i = start; i < raw.length; i++) {
      if (raw[i].trim() !== '' && raw[i].length - raw[i].trimStart().length <= indent) break;
      body.push(raw[i]);
      end = i + 1;
    }
    while (pos < lines.length && lines[pos].line < end) pos++;
    const cut = Math.min(...body.filter((l) => l.trim() !== '').map((l) => l.length - l.trimStart().length));
    const out = body.map((l) => l.slice(cut)).join(style.startsWith('>') ? ' ' : '\n');
    return style.endsWith('-') ? out.replace(/\s+$/, '') : `${out.replace(/\s+$/, '')}\n`;
  };
  /** @param {number} indent @returns {any} */
  const block = (indent) => (lines[pos].text.startsWith('- ') || lines[pos].text === '-' ? sequence(indent) : mapping(indent));
  /** The value after `key:` on line `lines[pos - 1]`, whose own indentation is `indent`. @param {string} rest @param {number} indent */
  const valueAfter = (rest, indent) => {
    if (/^[|>][-+]?$/.test(rest)) return blockScalar(indent, rest);
    if (rest !== '') return scalar(rest);
    if (pos >= lines.length) return null;
    const next = lines[pos];
    if (next.indent > indent || (next.indent === indent && next.text.startsWith('- '))) return block(next.indent);
    return null;
  };
  /** @param {number} indent */
  function mapping(indent) {
    /** @type {Record<string, any>} */
    const out = {};
    while (pos < lines.length && lines[pos].indent === indent && !lines[pos].text.startsWith('- ')) {
      const m = /^("[^"]*"|'[^']*'|[^:]+?):(?:\s+(.*))?$/.exec(lines[pos].text);
      if (!m) throw new Error(`line ${lines[pos].line + 1}: not a mapping entry: ${lines[pos].text}`);
      pos++;
      out[String(scalar(m[1]))] = valueAfter(m[2] ?? '', indent);
    }
    if (pos < lines.length && lines[pos].indent > indent) throw new Error(`line ${lines[pos].line + 1}: unexpected indentation`);
    return out;
  }
  /** @param {number} indent */
  function sequence(indent) {
    const out = [];
    while (pos < lines.length && lines[pos].indent === indent && (lines[pos].text.startsWith('- ') || lines[pos].text === '-')) {
      const item = lines[pos].text === '-' ? '' : lines[pos].text.slice(2).trim();
      if (item === '') {
        pos++;
        out.push(pos < lines.length && lines[pos].indent > indent ? block(lines[pos].indent) : null);
      } else if (/^("[^"]*"|'[^']*'|[^:'"[\]{}]+?):(\s|$)/.test(item)) {
        // A mapping that starts on the item's line: read it as a mapping indented past the dash.
        lines[pos] = { ...lines[pos], indent: indent + 2, text: item };
        out.push(mapping(indent + 2));
      } else {
        pos++;
        out.push(scalar(item));
      }
    }
    return out;
  }
  const doc = block(lines[0].indent);
  if (pos < lines.length) throw new Error(`line ${lines[pos].line + 1}: not read`);
  return doc;
}

/**
 * Why the workflow does not publish a validated build on a push to main, as far as its structure shows: an empty
 * list when the structure is the one the claim states.
 * @param {string} text the workflow file
 * @returns {string[]}
 */
export function publishingProblems(text) {
  /** @type {string[]} */
  const problems = [];
  let wf;
  try {
    wf = readWorkflow(text);
  } catch (e) {
    return [`the workflow cannot be read: ${/** @type {Error} */ (e).message}`];
  }
  const on = wf?.on ?? wf?.[/** @type {any} */ ('true')];
  const push = on?.push;
  if (!push || typeof push !== 'object') problems.push('the workflow is not triggered by push');
  else {
    if (!Array.isArray(push.branches) || push.branches.length !== 1 || push.branches[0] !== 'main') problems.push('push is not limited to exactly the branch main');
    const extra = Object.keys(push).filter((k) => k !== 'branches');
    if (extra.length) problems.push(`push has a filter that can skip a push to main: ${extra.join(', ')}`);
  }
  if (wf?.permissions?.pages !== 'write' || wf?.permissions?.['id-token'] !== 'write') problems.push('the workflow lacks pages: write and id-token: write');
  const build = wf?.jobs?.build;
  const deploy = wf?.jobs?.deploy;
  if (!build) return [...problems, 'there is no build job'];
  if (!deploy) return [...problems, 'there is no deploy job'];
  if (build.if !== undefined) problems.push(`the build job runs only if ${build.if}`);
  if (deploy.if !== undefined && deploy.if !== "github.ref == 'refs/heads/main'") problems.push(`the deploy job runs only if ${deploy.if}`);
  const needs = Array.isArray(deploy.needs) ? deploy.needs : deploy.needs === undefined ? [] : [deploy.needs];
  if (!needs.includes('build')) problems.push('the deploy job does not need the build job, so it can deploy without a validated build');
  for (const [name, job] of Object.entries(wf.jobs ?? {})) {
    if (/** @type {any} */ (job)?.['continue-on-error']) problems.push(`job ${name} continues on error`);
  }
  const steps = Array.isArray(build.steps) ? build.steps : [];
  /** @param {(s: any) => boolean} pred @param {string} what */
  const find = (pred, what) => {
    const i = steps.findIndex(pred);
    if (i < 0) problems.push(`the build job has no step that ${what}`);
    return i;
  };
  const lean = find((s) => typeof s?.run === 'string' && /tools\/build-formal-wasm\.js|npm run build:formal-wasm/.test(s.run), 'builds the Lean core');
  const validate = find((s) => typeof s?.run === 'string' && /node cli\/exegra\.js validate --project exegra\b/.test(s.run), 'validates the specification');
  const bundle = find((s) => typeof s?.run === 'string' && /\bvite build\b/.test(s.run), 'builds the bundle');
  const upload = find((s) => typeof s?.uses === 'string' && s.uses.startsWith('actions/upload-pages-artifact@'), 'uploads the Pages artifact');
  if (lean >= 0 && validate >= 0 && bundle >= 0 && upload >= 0 && !(lean < validate && validate < bundle && bundle < upload)) {
    problems.push('the build job does not build the Lean core, validate, build and upload in that order');
  }
  for (const i of [lean, validate, bundle, upload]) {
    if (i < 0) continue;
    const s = steps[i];
    if (s.if !== undefined) problems.push(`step ${i} of the build job runs only if ${s.if}`);
    if (s['continue-on-error']) problems.push(`step ${i} of the build job continues on error`);
    // A failure of these commands must fail the job: no second command and no ignored exit status.
    if (typeof s.run === 'string' && /\|\||;|&|\bset\s+\+e\b/.test(s.run)) problems.push(`step ${i} of the build job can hide a failure: ${s.run.trim()}`);
  }
  if (upload >= 0 && steps[upload]?.with?.path !== 'dist') problems.push('the uploaded artifact is not dist');
  const deploySteps = Array.isArray(deploy.steps) ? deploy.steps : [];
  const dep = deploySteps.findIndex((s) => typeof s?.uses === 'string' && s.uses.startsWith('actions/deploy-pages@'));
  if (dep < 0) problems.push('the deploy job has no deploy-pages step');
  else if (deploySteps[dep].if !== undefined) problems.push(`the deploy step runs only if ${deploySteps[dep].if}`);
  return problems;
}

/**
 * The five workflow edits of docs/assessment/2026-11-26/demos/pages-mutants.mjs under which no push to main
 * publishes a validated build, applied to the workflow as it is.
 * @param {string} orig
 */
function mutants(orig) {
  return {
    'deploy job never runs': orig.replace("if: github.ref == 'refs/heads/main'", 'if: false'),
    'validation failure ignored': orig.replace('validate --project exegra --pretty', 'validate --project exegra --pretty || true'),
    'push limited to a path that never changes': orig.replace('branches: [main]', 'branches: [main]\n    paths: [does-not-exist/**]'),
    'deploy no longer waits for build': orig.replace('    needs: build\n', ''),
    'build job disabled': orig.replace('    runs-on: ubuntu-latest\n    steps:', '    if: false\n    runs-on: ubuntu-latest\n    steps:'),
  };
}

// The Vite configuration's base is relative.
// @evidence pages-site-published-from-main
test('the production build uses relative asset URLs so it loads under a sub-path', async () => {
  const config = (await import('../../vite.config.js')).default;
  assert.equal(config.base, './');
});

// The workflow's push trigger names exactly the branch main and no other filter, and it grants pages: write and id-token: write.
// @evidence pages-site-published-from-main
test('the Pages workflow is triggered by a push to main with no path or tag filter and may deploy to Pages', () => {
  const problems = publishingProblems(workflowText);
  const trigger = problems.filter((p) => /push|pages: write/.test(p));
  assert.deepEqual(trigger, []);
});

// Read structurally: the build job has no condition and builds the Lean core, validates specs/exegra/spec.jsonc, builds and uploads dist in that order, none of these steps conditional or able to hide a failure; the deploy job needs build, runs only on main and deploys.
// @evidence pages-site-published-from-main
test('the Pages workflow builds the Lean core and validates the specification before it builds and deploys dist', () => {
  assert.deepEqual(publishingProblems(workflowText), []);
});

// The checks of the two workflow tests fail on each of the five mutants of docs/assessment/2026-11-26/demos/pages-mutants.mjs applied to the workflow as it is: if: false on the deploy or the build job, || true after validate, a never-matching paths filter, needs: build removed.
// @evidence pages-site-published-from-main
test('the workflow checks fail on each of the five publishing mutants', () => {
  for (const [name, text] of Object.entries(mutants(workflowText))) {
    assert.notEqual(text, workflowText, `the mutation "${name}" applies to the workflow as it is`);
    assert.ok(publishingProblems(text).length > 0, `the checks refuse the mutant "${name}"`);
  }
});
