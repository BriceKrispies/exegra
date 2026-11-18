import Exegra.Value

/-
JSON text to values and back, with `JSON.parse` and `JSON.stringify` semantics
(`parse_json` and `write_json` in `engine/exegra-engine/src/value.rs`).

Lean's `Lean.Data.Json` keeps object members in a sorted map, which loses the property order the
semantics depends on (see `Exegra/Value.lean`), and it does not promise correctly rounded
numbers. So reading and writing are done here, over the standard library alone:

- objects keep JavaScript property order; a repeated key keeps the first position and the last
  value, as in `JSON.parse`;
- numbers are rounded once, correctly (`Num.ofDecimal`);
- numbers are written as the shortest text that reads back to the same double, non-finite
  numbers as `null`, as `JSON.stringify` does; `undefined` properties are left out and
  `undefined` array items are written as `null`.

The detail text of a JSON syntax error is not part of the contract (the engine's comes from
serde_json); only the prefix `the input is not JSON:` is.
-/

namespace Exegra.Json

abbrev P := StateT (List Char) (Except String)

private def fail {α} (msg : String) : P α := throw msg

private def peek : P (Option Char) := do return (← get).head?

private def advance : P Unit := modify List.tail

private partial def skipWs : P Unit := do
  match ← peek with
  | some ' ' | some '\t' | some '\n' | some '\r' => advance; skipWs
  | _ => pure ()

private def expect (c : Char) : P Unit := do
  match ← peek with
  | some d => if d == c then advance else fail s!"expected '{c}', found '{d}'"
  | none => fail s!"expected '{c}', found the end"

private def literal (word : String) (v : Value) : P Value := do
  for c in word.toList do expect c
  return v

private partial def digits : P (List Char) := do
  match ← peek with
  | some c => if c.isDigit then do advance; return c :: (← digits) else return []
  | none => return []

private def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hex4 : P Nat := do
  let mut n := 0
  for _ in [0:4] do
    match ← peek with
    | some c => match hexVal c with
      | some d => advance; n := n * 16 + d
      | none => fail "bad \\u escape"
    | none => fail "bad \\u escape"
  return n

private def number : P Value := do
  let neg ← do
    if (← peek) == some '-' then advance; pure true else pure false
  let intPart ← digits
  if intPart.isEmpty then fail "invalid number"
  if intPart.length > 1 && intPart.head? == some '0' then fail "invalid number"
  let frac ← do
    if (← peek) == some '.' then
      advance
      let f ← digits
      if f.isEmpty then fail "invalid number"
      pure f
    else pure []
  let ex : Int ← do
    match ← peek with
    | some 'e' | some 'E' =>
      advance
      let sgn ← do
        match ← peek with
        | some '-' => advance; pure (-1 : Int)
        | some '+' => advance; pure 1
        | _ => pure 1
      let ds ← digits
      if ds.isEmpty then fail "invalid number"
      pure (sgn * (Num.digitsToNat ds : Int))
    | _ => pure 0
  let m := Num.digitsToNat (intPart ++ frac)
  return .num (Num.ofDecimal neg m (ex - frac.length))

private partial def stringBody (acc : List Char) : P String := do
  match ← peek with
  | none => fail "unterminated string"
  | some '"' => advance; return String.ofList acc.reverse
  | some '\\' =>
    advance
    match ← peek with
    | some '"' => advance; stringBody ('"' :: acc)
    | some '\\' => advance; stringBody ('\\' :: acc)
    | some '/' => advance; stringBody ('/' :: acc)
    | some 'b' => advance; stringBody ('\x08' :: acc)
    | some 'f' => advance; stringBody ('\x0c' :: acc)
    | some 'n' => advance; stringBody ('\n' :: acc)
    | some 'r' => advance; stringBody ('\r' :: acc)
    | some 't' => advance; stringBody ('\t' :: acc)
    | some 'u' =>
      advance
      let hi ← hex4
      if 0xD800 ≤ hi && hi < 0xDC00 then
        expect '\\'; expect 'u'
        let lo ← hex4
        if !(0xDC00 ≤ lo && lo < 0xE000) then fail "lone surrogate"
        let cp := 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)
        stringBody (Char.ofNat cp :: acc)
      else if 0xDC00 ≤ hi && hi < 0xE000 then fail "lone surrogate"
      else stringBody (Char.ofNat hi :: acc)
    | _ => fail "bad escape"
  | some c =>
    if c.toNat < 0x20 then fail "control character in string"
    else do advance; stringBody (c :: acc)

private def string : P String := do
  expect '"'
  stringBody []

mutual
private partial def value : P Value := do
  skipWs
  match ← peek with
  | some '{' => advance; object []
  | some '[' => advance; array []
  | some '"' => return .str (← string)
  | some 't' => literal "true" (.bool true)
  | some 'f' => literal "false" (.bool false)
  | some 'n' => literal "null" .null
  | some c => if c == '-' || c.isDigit then number else fail s!"unexpected '{c}'"
  | none => fail "unexpected end"

private partial def object (fs : List (String × Value)) : P Value := do
  skipWs
  if (← peek) == some '}' && fs.isEmpty then advance; return .obj 0 fs
  skipWs
  let k ← string
  skipWs
  expect ':'
  let v ← value
  let fs := objInsert fs k v
  skipWs
  match ← peek with
  | some ',' => advance; object' fs
  | some '}' => advance; return .obj 0 fs
  | _ => fail "expected ',' or '}'"

private partial def object' (fs : List (String × Value)) : P Value := do
  skipWs
  let k ← string
  skipWs
  expect ':'
  let v ← value
  let fs := objInsert fs k v
  skipWs
  match ← peek with
  | some ',' => advance; object' fs
  | some '}' => advance; return .obj 0 fs
  | _ => fail "expected ',' or '}'"

private partial def array (xs : List Value) : P Value := do
  skipWs
  if (← peek) == some ']' && xs.isEmpty then advance; return .arr 0 []
  let v ← value
  skipWs
  match ← peek with
  | some ',' => advance; array' (v :: xs)
  | some ']' => advance; return .arr 0 (v :: xs).reverse
  | _ => fail "expected ',' or ']'"

private partial def array' (xs : List Value) : P Value := do
  let v ← value
  skipWs
  match ← peek with
  | some ',' => advance; array' (v :: xs)
  | some ']' => advance; return .arr 0 (v :: xs).reverse
  | _ => fail "expected ',' or ']'"
end

/-- Parse JSON text (a leading byte-order mark is skipped, as the engine does). -/
def parse (text : String) : Except String Value :=
  let cs := text.toList
  let cs := if cs.head? == some '﻿' then cs.tail else cs
  match (do let v ← value; skipWs; pure v : P Value).run cs with
  | .ok (v, rest) =>
    if rest.isEmpty then .ok v else .error "the input is not JSON: trailing characters"
  | .error e => .error s!"the input is not JSON: {e}"

/-- One character of a string as JSON, with the escape `JSON.stringify` uses for it. -/
def escape (c : Char) : String :=
  match c with
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | '\x08' => "\\b"
  | '\x0c' => "\\f"
  | c =>
    if c.toNat < 0x20 then
      let h := Nat.toDigits 16 c.toNat
      "\\u" ++ String.ofList (List.replicate (4 - h.length) '0' ++ h)
    else c.toString

/-- A string as JSON, with the escapes `JSON.stringify` uses. -/
def quote (s : String) : String :=
  "\"" ++ s.toList.foldl (fun acc c => acc ++ escape c) "" ++ "\""

/-- A number as JSON: the shortest text reading back to it; non-finite values are `null`. -/
def number' (x : Float) : String :=
  if x.isFinite then Num.jsNumberToString x else "null"

mutual
/-- Compact JSON text of a value. A total function, by structural recursion; `undefined`
properties are left out. -/
def write : Value → String
  | .undef => "null"
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num x => number' x
  | .str s => quote s
  | .arr _ xs => "[" ++ ",".intercalate (writeItems xs) ++ "]"
  | .obj _ fs => "{" ++ ",".intercalate (writeMembers fs) ++ "}"

/-- The JSON texts of array items. -/
def writeItems : List Value → List String
  | [] => []
  | x :: xs => write x :: writeItems xs

/-- The JSON texts `"key":value` of an object's members, leaving out `undefined` ones. -/
def writeMembers : List (String × Value) → List String
  | [] => []
  | (k, v) :: fs =>
    match v with
    | .undef => writeMembers fs
    | _ => (quote k ++ ":" ++ write v) :: writeMembers fs
end

end Exegra.Json
