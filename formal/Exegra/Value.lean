import Exegra.Number

/-
Values of the simulation, with the semantics of the JavaScript values the reference engine
held (`engine/exegra-engine/src/value.rs`).

- Numbers are IEEE 754 doubles (`Float`).
- Objects keep JavaScript's property order: canonical array-index keys first, ascending, then
  the other keys in insertion order. The order is observable: the entries of an `emit` payload
  are evaluated in it, so it decides which error a payload with two failing entries reports.
- Arrays and objects are references in JavaScript and `===` compares them by identity. The
  engine reproduces this with shared `Rc`s. Here every array and object carries an identity
  `id`; a deep copy (`Value.copy`) gives every array and object inside a fresh identity, and
  passing a value on (a reference resolved by an expression, assigned by `set`) keeps it. Two
  compound values are strictly equal exactly when their identities are. Identities of values
  read from the input are 0 and never observed: the engine copies every input literal before
  it can reach an expression.
- `undef` exists only where JavaScript can hold `undefined`: a variable declared without an
  initial value. JSON output leaves it out as an object property.
-/

namespace Exegra

inductive Value where
  | undef
  | null
  | bool (b : Bool)
  | num (x : Float)
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

/-- JavaScript's strict equality `===`: IEEE equality for numbers (NaN differs from itself,
0 equals -0), identity for arrays and objects. -/
def strictEq : Value → Value → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr i _, .arr j _ => i == j
  | .obj i _, .obj j _ => i == j
  | _, _ => false

/-- `x === undefined || x === null`. -/
def isNullish : Value → Bool
  | .undef => true
  | .null => true
  | _ => false

def asString? : Value → Option String
  | .str s => some s
  | _ => none

def asNumber? : Value → Option Float
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

end Exegra
