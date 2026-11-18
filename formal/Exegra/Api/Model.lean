import Exegra.Api.Basic
import Exegra.Model

/-!
Model derivation and the semantic hash at the call boundary (`src/core/parse.js`,
`src/core/hash.js`).

- `model.derive`: `{spec, metamodel, methods}` to `{diagnostics, model}`; the document is
  encoded as `Exegra.Model.decode` reads it, every location is a raw path (`at`, `part`) that
  the shell maps to a source position.
- `hash.normalize` and `hash.semantic`: `{schemaVersion, vocabulary, entities: [{id, kind, data}]}`
  (the top-level declarations) to the normal form, and to the semantic hash.
-/

namespace Exegra.Api.ModelPort

open Exegra Exegra.Model

/-- The top-level declarations of a hash request. -/
def decls (args : Value) : List Hash.Decl :=
  (itemsOf (get args "entities")).map fun e =>
    (segKey (get e "id"), segKey (get e "kind"), get e "data")

def normalizeValue (args : Value) : Except String String :=
  .ok (Impl.JsonOut.write' (Hash.normalize' (get args "schemaVersion") (get args "vocabulary") (decls args)))

def semanticValue (args : Value) : Except String String :=
  .ok (Json.quote (Hash.semanticHash' (get args "schemaVersion") (get args "vocabulary") (decls args)))

def entries : List Entry := [
  { name := "model.derive",
    doc := "{spec, metamodel, methods} (spec encoded as Exegra.Model.decode reads it) to {diagnostics, model} with raw paths for locations.",
    fn := deriveValue },
  { name := "hash.normalize",
    doc := "{schemaVersion, vocabulary, entities: [{id, kind, data}]} to the normal form of the model.",
    fn := normalizeValue },
  { name := "hash.semantic",
    doc := "{schemaVersion, vocabulary, entities: [{id, kind, data}]} to the semantic hash (14 hex digits).",
    fn := semanticValue }
]

end Exegra.Api.ModelPort
