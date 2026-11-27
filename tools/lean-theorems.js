// Checks theorems of the Lean core (formal/) for `lean-theorem` claims. Node-only.
//
// For each requested theorem, Lean itself (the toolchain of formal/lean-toolchain, through
// `lake env lean` in formal/, on the built library) reports:
//   - whether the constant exists and is a theorem;
//   - whether the Lean kernel accepts its proof again: the proof term is re-added under a fresh name
//     with `addDecl`, which type-checks it in the kernel;
//   - the axioms it depends on (`Lean.collectAxioms`, what `#print axioms` prints);
//   - for each named implementation constant: whether it exists, its kind, and whether it occurs in
//     the theorem's statement (its type);
//   - the statement itself as Lean prints it, recorded as its sha256 (statementHash).
// Each record also carries the hash of the formal/ sources it was checked on (formalHash) and the
// records stamp of the tree (stamp), so a later read can tell a check of other sources from a fresh one.
// These facts are recorded as they are; the status they give a claim is decided by
// src/core/claims.js (method `lean-theorem`), so the application derives the same status from the
// recorded facts without Lean.
//
// checkTheorems(requests, opts) -> {available: true, lean, checkedAt, results} | {available: false, reason}
//   requests: [{theorem, about: [constant]}]; opts.prelude: Lean declarations elaborated before the
//   check, after `import Exegra` (tests use it for theorems that must be refused).

import { createHash } from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { formalSourcesHash, recordsStamp } from './tree-stamp.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const FORMAL = path.join(ROOT, 'formal');
const MARK = 'EXEGRA-THEOREM ';
const NAME = /^[A-Za-z_][A-Za-z0-9_'.]*$/;

/**
 * @typedef {{theorem: string, about?: string[]}} TheoremRequest
 * @typedef {{found: boolean, kind?: string, kernel?: string, axioms?: string[], about?: Record<string, {kind: string, inStatement: boolean}>, lean?: string, checkedAt?: string,
 *   statementHash?: string, formalHash?: string, stamp?: string}} TheoremRecord
 *   statementHash: sha256 of the theorem's type as Lean printed it; formalHash: tools/tree-stamp.js formalSourcesHash
 *   of the sources checked; stamp: the records stamp of the tree
 */

/** Lean's name syntax for a dotted name, with «» around components that need it. @param {string} n */
function leanName(n) {
  return '`' + n.split('.').map((c) => (/^[A-Za-z_][A-Za-z0-9_']*$/.test(c) ? c : `«${c}»`)).join('.');
}

/** @param {string} s */
const leanString = (s) => JSON.stringify(s);

const CHECKER = String.raw`
open Lean Elab Command in
def exegraKind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .ctorInfo _ => "constructor" | .inductInfo _ => "inductive"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient"

open Lean Elab Command in
def exegraCheck (thm : Name) (about : List Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? thm with
  | none => IO.println ("${MARK}" ++ (Json.mkObj [("theorem", toJson thm.toString), ("found", toJson false)]).compress)
  | some ci =>
    let kernel ← match ci with
      | .thmInfo tv =>
        let fresh := Name.str thm "_exegra_recheck"
        try
          liftCoreM (addDecl (.thmDecl { tv with name := fresh, all := [fresh] }))
          pure "ok"
        catch e => pure s!"error: {← e.toMessageData.toString}"
      | _ => pure "not a theorem"
    let axioms ← liftCoreM (collectAxioms thm)
    let used := ci.type.getUsedConstants
    let aboutJson := about.map fun n =>
      let kind := match env.find? n with
        | some c => exegraKind c
        | none => "missing"
      (n.toString, Json.mkObj [("kind", toJson kind), ("inStatement", toJson (used.contains n))])
    IO.println ("${MARK}" ++ (Json.mkObj [("theorem", toJson thm.toString), ("found", toJson true),
      ("kind", toJson (exegraKind ci)), ("kernel", toJson kernel), ("statement", toJson (toString ci.type)),
      ("axioms", toJson (axioms.map (·.toString))), ("about", Json.mkObj aboutJson)]).compress)
`;

/** The toolchain version formal/ pins. */
function pinnedLean() {
  return (fs.readFileSync(path.join(FORMAL, 'lean-toolchain'), 'utf8').trim().match(/v([0-9.]+)$/) ?? [])[1] ?? 'unknown';
}

/**
 * Check theorems with Lean.
 * @param {TheoremRequest[]} requests
 * @param {{prelude?: string, build?: boolean}} [opts]  build: run `lake build` first (default true)
 * @returns {{available: true, lean: string, checkedAt: string, results: Record<string, TheoremRecord>} | {available: false, reason: string}}
 */
export function checkTheorems(requests, opts = {}) {
  // Asked from formal/, where formal/lean-toolchain selects the toolchain: elan's lake proxy fails
  // elsewhere when no default toolchain is set, though lake works for the Lean project.
  const lake = spawnSync('lake', ['--version'], { cwd: FORMAL, encoding: 'utf8', windowsHide: true });
  if (lake.error || lake.status !== 0) return { available: false, reason: `lake is not available in formal/ (install elan with the toolchain of formal/lean-toolchain)${lake.stderr ? `: ${String(lake.stderr).trim().split('\n')[0]}` : ''}` };
  for (const r of requests) {
    for (const n of [r.theorem, ...(r.about ?? [])]) if (!NAME.test(n)) return { available: false, reason: `"${n}" is not a Lean constant name` };
  }
  if (opts.build !== false) {
    const b = spawnSync('lake', ['build', 'Exegra'], { cwd: FORMAL, encoding: 'utf8', windowsHide: true, maxBuffer: 1 << 26 });
    if (b.status !== 0) return { available: false, reason: `lake build failed:\n${String(b.stdout ?? '').slice(-2000)}${String(b.stderr ?? '').slice(-1000)}` };
  }
  const calls = requests.map((r) => `#eval exegraCheck ${leanName(r.theorem)} [${(r.about ?? []).map(leanName).join(', ')}]`);
  const text = ['import Exegra', 'import Lean', '', opts.prelude ?? '', CHECKER, ...calls, ''].join('\n');
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-theorems-'));
  try {
    const file = path.join(dir, 'Check.lean');
    fs.writeFileSync(file, text);
    const r = spawnSync('lake', ['env', 'lean', file], { cwd: FORMAL, encoding: 'utf8', windowsHide: true, maxBuffer: 1 << 26 });
    const out = String(r.stdout ?? '');
    /** @type {Record<string, TheoremRecord>} */
    const results = {};
    const checkedAt = new Date().toISOString();
    const lean = pinnedLean();
    // The stamps the check depends on: the Lean sources it ran on and the tree. A later read without Lean
    // compares formalHash with the current sources (src/core/claims.js) and reads a mismatch as stale.
    const formalHash = formalSourcesHash(ROOT);
    /** @type {string|null} */
    let stamp = null;
    try { stamp = recordsStamp(ROOT); } catch { stamp = null; }
    for (const line of out.split(/\r?\n/)) {
      if (!line.startsWith(MARK)) continue;
      const rec = JSON.parse(line.slice(MARK.length));
      const name = rec.theorem;
      delete rec.theorem;
      // The statement as Lean printed it is kept as its hash: what the theorem says, pinned for review.
      if (typeof rec.statement === 'string') {
        rec.statementHash = createHash('sha256').update(rec.statement, 'utf8').digest('hex');
        delete rec.statement;
      }
      results[name] = { ...rec, lean, checkedAt, formalHash, ...(stamp ? { stamp } : {}) };
    }
    // Elaboration errors in the prelude are reported, but checks after them still ran.
    const missing = requests.filter((q) => !results[q.theorem]);
    if (missing.length) {
      return { available: false, reason: `Lean did not report on ${missing.map((q) => q.theorem).join(', ')}:\n${(out + String(r.stderr ?? '')).slice(-3000)}` };
    }
    return { available: true, lean, checkedAt, results };
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}
