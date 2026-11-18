import Exegra.Json

/-!
The call boundary between Exegra's JavaScript shell and its Lean core: the shape of a function
the shell may call. `Exegra.Api` holds the registry and the one exported entry point.

A function takes its arguments as one JSON value (`Value`, parsed by `Exegra.Json`) and returns
the JSON text of its result, or an error message. Errors are values: a function never panics or
traps on bad arguments, it returns `.error`.
-/

namespace Exegra.Api

/-- A function callable from the shell: JSON arguments to the JSON text of the result. -/
abbrev Fn := Value → Except String String

/-- One registered function: the name the shell calls it by, what it does, and the function. -/
structure Entry where
  name : String
  doc : String
  fn : Fn

end Exegra.Api
