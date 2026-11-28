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
//   - the statement itself as Lean prints it with binder names erased, recorded as its sha256 (statementHash,
//     hashVersion 2), so that renaming a bound variable is not a change of statement;
//   - the file that defines the theorem and, for each constant of Exegra its statement uses, that constant and the
//     file that defines it (file, declarations: the dependency graph of exegra impact);
//   - for a request that names a `supersedes` theorem: whether it is a theorem the kernel accepts, its axioms,
//     whether its type is an implication whose premise is the theorem's statement (definitional equality), and its
//     conclusion, recorded as its sha256 (conclusionHash) to compare with the old statement hash (exegra admit).
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
import { formalSourcesHash, recordsStamp, factStamps } from './tree-stamp.js';
import { theoremFact } from '../src/core/facts.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const FORMAL = path.join(ROOT, 'formal');
const MARK = 'EXEGRA-THEOREM ';
const NAME = /^[A-Za-z_][A-Za-z0-9_'.]*$/;

/**
 * @typedef {{theorem: string, about?: string[], supersedes?: string}} TheoremRequest
 * @typedef {{found: boolean, kind?: string, kernel?: string, axioms?: string[], about?: Record<string, {kind: string, inStatement: boolean}>, lean?: string, checkedAt?: string,
 *   statementHash?: string, hashVersion?: number, formalHash?: string, stamp?: string, file?: string|null,
 *   declarations?: {name: string, file: string|null}[],
 *   supersedes?: {name: string, found: boolean, kind?: string, kernel?: string, axioms?: string[], premiseIsNew?: boolean, conclusionHash?: string}}} TheoremRecord
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

/-- The statement with every binder name erased and every binder made explicit: what is hashed. -/
partial def exegraNorm : Lean.Expr → Lean.Expr
  | .forallE _ t b _ => .forallE (.mkSimple "x") (exegraNorm t) (exegraNorm b) .default
  | .lam _ t b _ => .lam (.mkSimple "x") (exegraNorm t) (exegraNorm b) .default
  | .app f a => .app (exegraNorm f) (exegraNorm a)
  | .letE _ t v b nd => .letE (.mkSimple "x") (exegraNorm t) (exegraNorm v) (exegraNorm b) nd
  | .mdata _ e => exegraNorm e
  | .proj s i e => .proj s i (exegraNorm e)
  | e => e

open Lean in
/-- The repository path of the Lean file that defines a constant of the library; null for one declared elsewhere. -/
def exegraFile (env : Environment) (n : Name) : Json :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    if m.getRoot == .mkSimple "Exegra" then toJson ("formal/" ++ "/".intercalate (m.components.map (·.toString)) ++ ".lean") else Json.null
  | none => Json.null

open Lean Elab Command Meta in
/-- What a superseding theorem shows: a kernel-checked implication from the new statement to the old one. -/
def exegraSupersedes (s : Name) (newType : Expr) : CommandElabM Json := do
  let env ← getEnv
  match env.find? s with
  | none => pure (Json.mkObj [("name", toJson s.toString), ("found", toJson false)])
  | some ci =>
    let kernel ← match ci with
      | .thmInfo tv =>
        let fresh := Name.str s "_exegra_recheck"
        try
          liftCoreM (addDecl (.thmDecl { tv with name := fresh, all := [fresh] }))
          pure "ok"
        catch e => pure s!"error: {← e.toMessageData.toString}"
      | _ => pure "not a theorem"
    let axioms ← liftCoreM (collectAxioms s)
    let (premiseIsNew, conclusion) ← match ci.type with
      | .forallE _ p q _ =>
        if q.hasLooseBVars then pure (false, "")
        else
          let same ← liftTermElabM (isDefEq p newType)
          pure (same, toString (exegraNorm q))
      | _ => pure (false, "")
    pure (Json.mkObj [("name", toJson s.toString), ("found", toJson true), ("kind", toJson (exegraKind ci)),
      ("kernel", toJson kernel), ("axioms", toJson (axioms.map (·.toString))),
      ("premiseIsNew", toJson premiseIsNew), ("conclusion", toJson conclusion)])

open Lean Elab Command in
def exegraCheck (thm : Name) (about : List Name) (supersedes : Option Name := none) : CommandElabM Unit := do
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
    let decls := (used.toList.filter fun n => (n.toString.startsWith "Exegra.")).map fun n =>
      Json.mkObj [("name", toJson n.toString), ("file", exegraFile env n)]
    let sup ← match supersedes with
      | none => pure Json.null
      | some s => exegraSupersedes s ci.type
    IO.println ("${MARK}" ++ (Json.mkObj [("theorem", toJson thm.toString), ("found", toJson true),
      ("kind", toJson (exegraKind ci)), ("kernel", toJson kernel), ("statement", toJson (toString (exegraNorm ci.type))),
      ("axioms", toJson (axioms.map (·.toString))), ("about", Json.mkObj aboutJson),
      ("file", exegraFile env thm), ("declarations", Json.arr decls.toArray), ("supersedes", sup)]).compress)
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
    for (const n of [r.theorem, ...(r.about ?? []), ...(r.supersedes ? [r.supersedes] : [])]) if (!NAME.test(n)) return { available: false, reason: `"${n}" is not a Lean constant name` };
  }
  if (opts.build !== false) {
    const b = spawnSync('lake', ['build', 'Exegra'], { cwd: FORMAL, encoding: 'utf8', windowsHide: true, maxBuffer: 1 << 26 });
    if (b.status !== 0) return { available: false, reason: `lake build failed:\n${String(b.stdout ?? '').slice(-2000)}${String(b.stderr ?? '').slice(-1000)}` };
  }
  const calls = requests.map((r) => `#eval exegraCheck ${leanName(r.theorem)} [${(r.about ?? []).map(leanName).join(', ')}]${r.supersedes ? ` (some ${leanName(r.supersedes)})` : ''}`);
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
        rec.hashVersion = 2;
        delete rec.statement;
      }
      if (rec.supersedes && typeof rec.supersedes === 'object') {
        if (typeof rec.supersedes.conclusion === 'string' && rec.supersedes.conclusion) rec.supersedes.conclusionHash = createHash('sha256').update(rec.supersedes.conclusion, 'utf8').digest('hex');
        delete rec.supersedes.conclusion;
      } else delete rec.supersedes;
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

/**
 * The fact one recorded theorem check makes about a lean-theorem claim (Exegra.Verdict.Fact, kind leanTheorem):
 * the check and the claim's `about` constants, stamped with the formal/ hash the check ran on against the current
 * one. Lean decides its outcome (Exegra.Verdict.theoremOutcome).
 * @param {string} claimId @param {TheoremRecord} check @param {string[]} about
 * @param {{tree: string|null, formal: string|null}} current the current stamps (tools/tree-stamp.js currentStamps)
 */
export function theoremCheckFact(claimId, check, about, current) {
  return theoremFact(claimId, check, about, factStamps(check.formalHash, current, 'formal'));
}
