import Exegra.Format2
import Exegra.Prove
import Exegra.Temporal

/-!
The wasm module's single entry point: the same dispatch as `formal/Main.lean`, without stdin and
stdout. The result's first character says how it ended: `o` then the trace (or explorer result),
or `e` then the refusal message.
-/

open Exegra

@[export exegra_wasm_run]
def wasmRun (mode : UInt32) (text : String) : String :=
  let run := if mode == 1 then runExplore else if mode == 2 then runTemporal else runAny
  match run text with
  | .ok out => "o" ++ out
  | .error msg => "e" ++ msg
