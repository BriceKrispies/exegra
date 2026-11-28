import Exegra.Format2
import Exegra.Integrity
import Exegra.Impl.Semantics
import Exegra.Elab
import Exegra.ProveB
import Exegra.Api
import Exegra.ProveLive
import Exegra.ProveKernel

/-!
`exegra-lean`: reads one engine input JSON on stdin and writes one trace JSON on stdout, the
protocol of `exegra-sim` and of `tools/conformance.js --engine "<command>"`. Input that cannot be
run gives exit status 1 and the refusal message on stderr.

`exegra-lean explore` reads one exploration request instead (`Exegra.runExplore`: an engine
input, state invariants, a bound and a state budget) and writes the explorer's result for each
invariant; `exegra prove` uses it to find the results its generated proof file then states.
`exegra-lean liveness` decides liveness claims (`Exegra.V2.ProveLive.runLiveness`), and
`exegra-lean certificate` lists the states of a closed exploration as Lean terms, for the
closed-set certificate of an invariant. `exegra-lean module` writes a module that the kernel checks
with the standard axioms only (`Exegra.V2.ProveKernel.kernelModule`).

`exegra-lean call` reads one call-boundary request `{fn, args}` and writes the reply
(`Exegra.Api.handle`), as the WebAssembly core answers it.

`exegra-lean integrity` reads facts and integrity rules (`Exegra.Integrity.runIntegrity`) and
writes, per rule, whether it holds and every witness; `exegra prove-integrity` compares that with
the JavaScript evaluator.
-/

open Exegra

partial def readAll (h : IO.FS.Stream) (acc : ByteArray) : IO ByteArray := do
  let chunk ← h.read 65536
  if chunk.isEmpty then return acc else readAll h (acc ++ chunk)

def main (args : List String) : IO UInt32 := do
  let bytes ← readAll (← IO.getStdin) ByteArray.empty
  match String.fromUTF8? bytes with
  | none =>
    IO.eprintln "exegra-lean: the input is not JSON: not UTF-8"
    return 1
  | some text =>
    let run := if args == ["explore"] then V2.ProveB.runExplore else if args == ["temporal"] then V2.ProveB.runTemporal
      else if args == ["liveness"] then V2.ProveLive.runLiveness else if args == ["certificate"] then V2.ProveLive.runCertificate
      else if args == ["module"] then V2.ProveKernel.runKernelModule
      else if args == ["integrity"] then Integrity.runIntegrity
      else if args == ["--legacy"] then runAnyLegacy
      else if args == ["call"] then (fun t => .ok (Api.handle t))
      else if args == ["elab"] then (fun t => do V2.Elab.elabJson (← Json.parse t)) else Impl.runAny
    match run text with
    | .ok out =>
      let stdout ← IO.getStdout
      stdout.putStr out
      stdout.putStr "\n"
      stdout.flush
      return 0
    | .error msg =>
      IO.eprintln s!"exegra-lean: {msg}"
      return 1
