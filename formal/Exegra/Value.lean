import Exegra.Number

/-
Values of the simulation, with the semantics of the JavaScript values the reference engine
held (`engine/exegra-engine/src/value.rs`).

- Numbers are exact rationals (`Rat`, WG-5683): a JSON number is the exact value of its text
  (`Num.ofDecimal`), and is written as JavaScript writes the double nearest to it
  (`Num.jsNumberToString`).
- Objects keep JavaScript's property order: canonical array-index keys first, ascending, then
  the other keys in insertion order. The order is observable: the entries of an `emit` payload
  are evaluated in it, so it decides which error a payload with two failing entries reports.
- Every array and object carries an identity `id`; a deep copy (`Value.copy`) gives every
  array and object inside a fresh identity, and passing a value on (a reference resolved by an
  expression, assigned by `set`) keeps it. Identities are bookkeeping only: equality (`eqv`) is
  structural (WG-4902), as it is in generated code, so no identity is observable.
- `undef` exists only where JavaScript can hold `undefined`: a variable declared without an
  initial value. JSON output leaves it out as an object property.
-/

namespace Exegra

inductive Value where
  | undef
  | null
  | bool (b : Bool)
  | num (x : Rat)
  | str (s : String)
  | arr (id : Nat) (items : List Value)
  | obj (id : Nat) (fields : List (String × Value))
  deriving Inhabited

namespace Value

/-- JavaScript's `typeof`, with `null` reported as `"null"`, as the error messages do. -/
def typeName : Value → String
  | .undef => "undefined"
  | .null => "null"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .arr .. => "object"
  | .obj .. => "object"

/-- `x === undefined || x === null`. -/
def isNullish : Value → Bool
  | .undef => true
  | .null => true
  | _ => false

def asString? : Value → Option String
  | .str s => some s
  | _ => none

def asNumber? : Value → Option Rat
  | .num x => some x
  | _ => none

def asObject? : Value → Option (List (String × Value))
  | .obj _ fs => some fs
  | _ => none

end Value

/-- A canonical array index ("0", "1", ... up to 2^32 - 2), which JavaScript orders before
every other property key. -/
def arrayIndex? (key : String) : Option Nat :=
  let cs := key.toList
  if cs.isEmpty || cs.length > 10 || !cs.all Char.isDigit then none
  else if cs.length > 1 && cs.head? == some '0' then none
  else
    let n := Num.digitsToNat cs
    if n < 4294967295 then some n else none

/-- The value of an own property. -/
def objGet? (fs : List (String × Value)) (key : String) : Option Value :=
  (fs.find? (·.1 == key)).map (·.2)

def objHas (fs : List (String × Value)) (key : String) : Bool :=
  fs.any (·.1 == key)

/-- `o[key] = v`: an existing property keeps its position, a new one goes where JavaScript
puts it. -/
def objInsert (fs : List (String × Value)) (key : String) (v : Value) : List (String × Value) :=
  if objHas fs key then fs.map (fun (k, x) => if k == key then (k, v) else (k, x))
  else match arrayIndex? key with
    | none => fs ++ [(key, v)]
    | some n =>
      let before := fs.takeWhile (fun (k, _) => match arrayIndex? k with
        | some m => m < n
        | none => false)
      before ++ [(key, v)] ++ fs.drop before.length

/-- Replace the value of an existing property (no change when absent). -/
def objSet (fs : List (String × Value)) (key : String) (v : Value) : List (String × Value) :=
  fs.map (fun (k, x) => if k == key then (k, v) else (k, x))

mutual
/-- The reference engine's `deepCopy`: every array and object inside gets a fresh identity,
taken from the counter `n`; returns the copy and the next free identity. -/
def Value.copy : Value → Nat → Value × Nat
  | .arr _ xs, n =>
    let (ys, m) := Value.copyList xs (n + 1)
    (.arr n ys, m)
  | .obj _ fs, n =>
    let (gs, m) := Value.copyFields fs (n + 1)
    (.obj n gs, m)
  | .undef, n => (.undef, n)
  | .null, n => (.null, n)
  | .bool b, n => (.bool b, n)
  | .num x, n => (.num x, n)
  | .str s, n => (.str s, n)

def Value.copyList : List Value → Nat → List Value × Nat
  | [], n => ([], n)
  | x :: xs, n =>
    let (y, n1) := Value.copy x n
    let (ys, n2) := Value.copyList xs n1
    (y :: ys, n2)

def Value.copyFields : List (String × Value) → Nat → List (String × Value) × Nat
  | [], n => ([], n)
  | (k, x) :: fs, n =>
    let (y, n1) := Value.copy x n
    let (gs, n2) := Value.copyFields fs n1
    ((k, y) :: gs, n2)
end

mutual
/-- JavaScript's `String(v)`, for the values that can reach a refusal message. -/
def Value.display : Value → String
  | .undef => "undefined"
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num x => Num.jsNumberToString x
  | .str s => s
  | .arr _ xs => ",".intercalate (Value.displayItems xs)
  | .obj .. => "[object Object]"

def Value.displayItems : List Value → List String
  | [] => []
  | x :: xs => (if x.isNullish then "" else Value.display x) :: Value.displayItems xs
end


mutual
/-- Equality of values (`==`), structural (WG-4902, `docs/semantics.md`): numbers by value, strings and booleans by value, arrays element by element
in order, objects by their keys and members in any order. No value equals `undef`, except
`undef` itself, which never reaches a comparison (an unknown reference is an error first). -/
def Value.eqv : Value → Value → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr _ xs, .arr _ ys => Value.eqvItems xs ys
  | .obj _ fs, .obj _ gs => fs.length == gs.length && Value.eqvFields fs gs
  | _, _ => false

def Value.eqvItems : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => Value.eqv x y && Value.eqvItems xs ys
  | _, _ => false

/-- Every member of the first object is a member of the second with an equal value. Keys of an
object are distinct, so with equal lengths this is equality of the two key sets and values. -/
def Value.eqvFields : List (String × Value) → List (String × Value) → Bool
  | [], _ => true
  | (k, x) :: fs, gs =>
    (match objGet? gs k with
     | some y => Value.eqv x y
     | none => false) && Value.eqvFields fs gs
end

/-- The integer representation types (`src/core/builtin-types.js`). `u64` and `i64` are limited
to the integers a double holds exactly, `-(2^53 - 1) .. 2^53 - 1` (WG-4902). -/
inductive IntKind where
  | u8 | u16 | u32 | u64 | i32 | i64
  deriving DecidableEq, Hashable, Repr, Inhabited

def IntKind.name : IntKind → String
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64" | .i32 => "i32" | .i64 => "i64"

/-- The least value. -/
def IntKind.lo : IntKind → Rat
  | .u8 | .u16 | .u32 | .u64 => 0
  | .i32 => -2147483648
  | .i64 => -9007199254740991

/-- The greatest value. -/
def IntKind.hi : IntKind → Rat
  | .u8 => 255
  | .u16 => 65535
  | .u32 => 4294967295
  | .i32 => 2147483647
  | .u64 | .i64 => 9007199254740991

/-- The declared type of a reference, as far as evaluation depends on it (WG-4902). The engine
input gives it per behavior (`types`), lowered by `src/core/sim-input.js`: a timestamp is an
`i64` and a duration a `u64` (as generated code holds them), a declared id or scalar type its
representation, an `option<T>` or an optional payload field `option`. -/
inductive STy where
  /-- No declared type (a model-level variable, or a type evaluation does not depend on):
  numbers are exact rationals. -/
  | none
  /-- An integer type: arithmetic is checked integer arithmetic. -/
  | int (k : IntKind)
  /-- An option type: an absent value reads as `null`. -/
  | option
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The type a name in the engine input stands for; any other name is `none`. -/
def STy.ofName : String → STy
  | "u8" => .int .u8 | "u16" => .int .u16 | "u32" => .int .u32 | "u64" => .int .u64
  | "i32" => .int .i32 | "i64" => .int .i64
  | "option" => .option
  | _ => .none

/-- The declared types of references, by dotted path. -/
abbrev TyEnv := List String → STy

/-- No declared types. -/
def TyEnv.untyped : TyEnv := fun _ => .none

/-- Look a dotted path up in a list of declared types. -/
def tyLookup (tys : List (String × STy)) (path : List String) : STy :=
  match tys with
  | [] => .none
  | _ => ((tys.find? (·.1 == ".".intercalate path)).map (·.2)).getD .none

/-- The `types` member of a behavior in the engine input: `{path: typeName}`. -/
def tysOfValue : Value → List (String × STy)
  | .obj _ fs => fs.map fun (k, v) => (k, STy.ofName ((Value.asString? v).getD ""))
  | _ => []

end Exegra
