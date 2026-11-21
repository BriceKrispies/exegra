// Branch coverage of function examples (WG-4965): which branches of each function the examples of the
// specification take when Exegra evaluates them (src/core/function.js). docs/coverage.md.
//
// A branch is one outcome of a branch point of a function's lets and body:
//   if      "then" and "else"
//   match   each arm, by index ("arm:<i>"), a "_" arm included
//   try     "ok" (the value passes on) and "err" (the error propagates); "err" only when the called function can
//           fail at all (failVariants is not empty)
//   fail    "taken"
// Every example of every function is evaluated with the branch recorder of function.js attached. A branch is
// covered when some example takes it, directly or through a function the example's function calls.
//
// The coverage is information only (the cover-functions command). It is not a readiness rule: a rule asking for
// every branch to be taken pushes a specification toward one example per branch, and examples are checked by
// evaluating them, not made into a test per branch.

import { analyzeFunctions, runFunction, failVariants, callees, withBranchRecorder, resolvedExample } from './function.js';
import { FnEvalError, decodeValue, valueEq } from './function-value.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./function-syntax.js').FnAst} FnAst */
/** @typedef {{code: string, severity: 'error' | 'info', message: string, entityId: string}} Gap */

/**
 * @typedef {Object} Branch
 * @property {string} id        "<where>@<offset>:<outcome>", stable for a given text
 * @property {'if'|'match'|'try'|'fail'} kind
 * @property {string} outcome   then, else, arm:<i>, ok, err, taken
 * @property {string} label     the outcome as written: "then", "else", the arm's pattern, "ok", "err", "fail"
 * @property {string} where     "body" or "let <name>"
 * @property {number} offset    character offset of the branch in that text
 * @property {number} line      1-based line in that text
 * @property {number} column    1-based column in that text
 * @property {string} text      the text at the branch, up to 48 characters
 * @property {boolean} covered
 */

/**
 * @typedef {Object} FunctionCoverage
 * @property {string} id
 * @property {number|null} line      the function's line in the specification
 * @property {boolean} usable        the function and every function it calls have no finding, so its examples ran
 * @property {number} examples       examples stated
 * @property {number} failedExamples examples that did not give their stated result or error
 * @property {number} total
 * @property {number} covered
 * @property {Branch[]} branches
 */

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);

/** Line and column (1-based) of `offset` in `text`. @param {string} text @param {number} offset */
function lineColumn(text, offset) {
  const lines = text.slice(0, Math.max(0, offset)).split('\n');
  return { line: lines.length, column: lines[lines.length - 1].length + 1 };
}

/** The pattern of a match arm as written. @param {any} pat */
function patternText(pat) {
  if (pat.k === 'wild') return '_';
  if (pat.bind !== undefined) return `${pat.name}(${pat.bind})`;
  if (pat.fields) return `${pat.name}{${pat.fields.map((/** @type {any} */ f) => (f.bind === f.field ? f.field : `${f.field}: ${f.bind}`)).join(', ')}}`;
  return pat.name;
}

/**
 * The branch points of one parsed text (a let or the body), in the order they are written, each with its
 * outcomes. A try of a function that cannot fail has only "ok".
 * @param {FnAst} root @param {Map<string, any>} sigs
 * @returns {{node: FnAst, kind: Branch['kind'], outcome: string, label: string, pos: number}[]}
 */
function branchPoints(root, sigs) {
  /** @type {{node: FnAst, kind: Branch['kind'], outcome: string, label: string, pos: number}[]} */
  const out = [];
  /** @param {any} x */
  const walk = (x) => {
    if (!x || typeof x !== 'object') return;
    if (Array.isArray(x)) { x.forEach(walk); return; }
    if (typeof x.t === 'string') {
      const n = /** @type {any} */ (x);
      const pos = typeof n.pos === 'number' ? n.pos : 0;
      if (n.t === 'if') {
        out.push({ node: n, kind: 'if', outcome: 'then', label: 'then', pos: typeof n.a?.pos === 'number' ? n.a.pos : pos });
        out.push({ node: n, kind: 'if', outcome: 'else', label: 'else', pos: typeof n.b?.pos === 'number' ? n.b.pos : pos });
      } else if (n.t === 'match') {
        n.arms.forEach((/** @type {any} */ arm, /** @type {number} */ i) => out.push({ node: n, kind: 'match', outcome: `arm:${i}`, label: patternText(arm.pat), pos: typeof arm.pos === 'number' ? arm.pos : pos }));
      } else if (n.t === 'try') {
        out.push({ node: n, kind: 'try', outcome: 'ok', label: 'ok', pos });
        const canFail = n.e?.t !== 'call' || failVariants(sigs, n.e.fn).length > 0;
        if (canFail) out.push({ node: n, kind: 'try', outcome: 'err', label: 'err', pos });
      } else if (n.t === 'builtin' && n.name === 'fail') {
        out.push({ node: n, kind: 'fail', outcome: 'taken', label: 'fail', pos });
      }
    }
    for (const [k, v] of Object.entries(x)) if (k !== 'ty' && k !== 'res' && v && typeof v === 'object') walk(v);
  };
  walk(root);
  return out;
}

/**
 * Whether one example gives what it states: evaluated with the recorder attached by the caller. Malformed examples
 * (reported by function.example-failed) and evaluation errors count as failed.
 * @param {Model} model @param {any} s the signature @param {Map<string, any>} sigs @param {any} ex
 * @returns {boolean}
 */
function runExample(model, s, sigs, ex) {
  if (!isObj(ex) || !isObj(ex.args) || ('result' in ex) === ('error' in ex)) return false;
  if (Object.keys(ex.args).some((k) => !s.params.some((/** @type {any} */ p) => p.name === k))) return false;
  if ('error' in ex && !s.errors) return false;
  try {
    // Fixture references (exampleFixtures) become the fixture's value first; one that cannot is a failed example.
    const r = resolvedExample(model, s, ex);
    const args = s.params.map((/** @type {any} */ p, /** @type {number} */ k) => decodeValue(p.type, r.args[k], `args.${p.name}`));
    const got = runFunction(model, s, sigs, args);
    if ('result' in ex) return 'value' in got && valueEq(got.value, decodeValue(s.returns, r.result, 'result'));
    return 'error' in got && valueEq(got.error, decodeValue(s.errors, r.error, 'error'));
  } catch (e) {
    if (e instanceof FnEvalError) return false;
    if (e instanceof Error && /^(example.fixture-[a-z]+|a fixture with a wrong value)/.test(e.message)) return false;
    throw e;
  }
}

/**
 * The branch coverage of every function of the model by its examples, in declaration order.
 * @param {Model} model
 * @returns {FunctionCoverage[]}
 */
export function functionCoverage(model) {
  const { sigs } = analyzeFunctions(model);
  /** @type {Map<FnAst, Set<string>>} */
  const hits = new Map();
  /** @type {Map<string, number>} */
  const failed = new Map();
  const usable = (/** @type {any} */ s) => s.ok && [...callees(sigs, s.fn.id)].every((c) => sigs.get(c)?.ok);
  withBranchRecorder((node, outcome) => {
    let set = hits.get(node);
    if (!set) hits.set(node, (set = new Set()));
    set.add(outcome);
  }, () => {
    for (const s of sigs.values()) {
      if (!usable(s)) continue;
      for (const ex of list(s.fn.data.examples)) if (!runExample(model, s, sigs, ex)) failed.set(s.fn.id, (failed.get(s.fn.id) ?? 0) + 1);
    }
  });
  /** @type {FunctionCoverage[]} */
  const out = [];
  for (const s of sigs.values()) {
    const d = s.fn.data;
    /** @type {{where: string, text: string, ast: FnAst|undefined}[]} */
    const parts = [
      ...list(d.let).map((l, i) => ({ where: `let ${isObj(l) ? l.name : i + 1}`, text: isObj(l) && typeof l.expr === 'string' ? l.expr : '', ast: s.lets[i] })),
      { where: 'body', text: typeof d.body === 'string' ? d.body : '', ast: s.body },
    ];
    /** @type {Branch[]} */
    const branches = [];
    const ok = usable(s);
    if (s.ok) {
      for (const part of parts) {
        if (!part.ast) continue;
        for (const b of branchPoints(part.ast, sigs)) {
          const { line, column } = lineColumn(part.text, b.pos);
          branches.push({
            id: `${part.where}@${b.pos}:${b.outcome}`, kind: b.kind, outcome: b.outcome, label: b.label, where: part.where,
            offset: b.pos, line, column, text: part.text.slice(b.pos, b.pos + 48), covered: !!hits.get(b.node)?.has(b.outcome),
          });
        }
      }
    }
    out.push({
      id: s.fn.id, line: s.fn.loc?.line ?? null, usable: ok, examples: list(d.examples).length, failedExamples: failed.get(s.fn.id) ?? 0,
      total: branches.length, covered: branches.filter((b) => b.covered).length, branches,
    });
  }
  return out;
}

/** A branch as a message names it. @param {Branch} b */
export function branchText(b) {
  const what = b.kind === 'if' ? `the ${b.outcome} branch of if` : b.kind === 'match' ? `the arm ${b.label}` : b.kind === 'try' ? (b.outcome === 'err' ? 'the error path of try' : 'the value path of try') : 'the fail';
  return `${what} (${b.where}, line ${b.line} column ${b.column}: "${b.text.length > 32 ? `${b.text.slice(0, 32)}...` : b.text}")`;
}
