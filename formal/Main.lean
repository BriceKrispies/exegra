import Exegra.Semantics
import Exegra.Temporal
import Exegra.Prove
import Exegra.Format2
import Exegra.Impl.Semantics

/-!
`exegra-lean`: reads one engine input JSON on stdin and writes one trace JSON on stdout, the
protocol of `exegra-sim` and of `tools/conformance.js --engine "<command>"`. Input that cannot be
run gives exit status 1 and the refusal message on stderr.

`exegra-lean explore` reads one exploration request instead (`Exegra.runExplore`: an engine
input, state invariants, a bound and a state budget) and writes the explorer's result for each
invariant; `exegra prove` uses it to find the results its generated proof file then states.
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
    let run := if args == ["explore"] then runExplore else if args == ["temporal"] then runTemporal else Impl.runAny
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
