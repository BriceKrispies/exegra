import Std.Data.HashSet
import Exegra.Value

/-
JSON text to values and back, with `JSON.parse` and `JSON.stringify` semantics
(`parse_json` and `write_json` in `engine/exegra-engine/src/value.rs`).

Lean's `Lean.Data.Json` keeps object members in a sorted map, which loses the property order the
semantics depends on (see `Exegra/Value.lean`), and it does not promise correctly rounded
numbers. So reading and writing are done here, over the standard library alone:

- objects keep JavaScript property order; a repeated key keeps the first position and the last
  value, as in `JSON.parse`;
- numbers are read exactly (`Num.ofDecimal`, an exact rational);
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

/-! ### The parser

The parser reads the UTF-8 bytes of the text by index (a `List Char` and a state monad per
character made a large request, such as the model a lowering reads, the dominant cost of a call).
It accepts and rejects exactly what the character parser above does: `charParse` is kept, and
`#guard`s at the end of this file check the two agree on a set of texts. An object's members are
collected in order and built with `objInsert` only when a key repeats or is an array index, so the
result is the one `objInsert` gives member by member. -/

namespace Fast

abbrev R := Except String

@[inline] def at! (s : ByteArray) (i : Nat) : UInt8 := if h : i < s.size then s[i] else 0

def isWs (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13
def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

partial def skipWs (s : ByteArray) (i : Nat) : Nat :=
  if i < s.size && isWs (at! s i) then skipWs s (i + 1) else i

partial def digitsEnd (s : ByteArray) (i : Nat) : Nat :=
  if i < s.size && isDigit (at! s i) then digitsEnd s (i + 1) else i

def natOf (s : ByteArray) (a b : Nat) : Nat := Id.run do
  let mut n := 0
  for k in [a:b] do n := n * 10 + (at! s k - 48).toNat
  return n

def number (s : ByteArray) (i : Nat) : R (Value × Nat) := do
  let neg := at! s i == 45
  let i := if neg then i + 1 else i
  let ie := digitsEnd s i
  if ie == i then throw "invalid number"
  if ie - i > 1 && at! s i == 48 then throw "invalid number"
  let (fa, fe) ← if at! s ie == 46 then do
      let fe := digitsEnd s (ie + 1)
      if fe == ie + 1 then throw "invalid number"
      pure (ie + 1, fe)
    else pure (ie, ie)
  let (ex, j) ← if fe < s.size && (at! s fe == 101 || at! s fe == 69) then do
      let k := fe + 1
      let (sgn, k) := if at! s k == 45 then ((-1 : Int), k + 1) else if at! s k == 43 then (1, k + 1) else (1, k)
      let de := digitsEnd s k
      if de == k then throw "invalid number"
      pure (sgn * (natOf s k de : Int), de)
    else pure ((0 : Int), fe)
  let m := natOf s i ie * 10 ^ (fe - fa) + natOf s fa fe
  return (.num (Num.ofDecimal neg m (ex - ((fe - fa : Nat) : Int))), j)

def hexVal (b : UInt8) : Option Nat :=
  if isDigit b then some (b - 48).toNat
  else if 97 ≤ b && b ≤ 102 then some (b - 87).toNat
  else if 65 ≤ b && b ≤ 70 then some (b - 55).toNat
  else none

def hex4 (s : ByteArray) (i : Nat) : R Nat := do
  let mut n := 0
  for k in [i:i + 4] do
    match hexVal (at! s k) with
    | some d => n := n * 16 + d
    | none => throw "bad \\u escape"
  return n

/-- The text of bytes `[a, b)`, which lie between ASCII bytes of a valid UTF-8 text. -/
def slice (s : ByteArray) (a b : Nat) : String :=
  if a == b then "" else (String.fromUTF8? (s.extract a b)).getD ""

/-- A string's body from `i` (after the opening quote): the string and the index after the closing
quote. -/
partial def stringBody (s : ByteArray) (i : Nat) (acc : String) : R (String × Nat) := do
  let rec run (j : Nat) : Nat :=
    if j < s.size then
      let b := at! s j
      if b == 34 || b == 92 || b < 32 then j else run (j + 1)
    else j
  let j := run i
  let acc := acc ++ slice s i j
  if j ≥ s.size then throw "unterminated string"
  let b := at! s j
  if b == 34 then return (acc, j + 1)
  if b < 32 then throw "control character in string"
  -- an escape
  let e := at! s (j + 1)
  if j + 1 ≥ s.size then throw "unterminated string"
  match e with
  | 34 => stringBody s (j + 2) (acc.push '"')
  | 92 => stringBody s (j + 2) (acc.push '\\')
  | 47 => stringBody s (j + 2) (acc.push '/')
  | 98 => stringBody s (j + 2) (acc.push '\x08')
  | 102 => stringBody s (j + 2) (acc.push '\x0c')
  | 110 => stringBody s (j + 2) (acc.push '\n')
  | 114 => stringBody s (j + 2) (acc.push '\r')
  | 116 => stringBody s (j + 2) (acc.push '\t')
  | 117 =>
    let hi ← hex4 s (j + 2)
    if 0xD800 ≤ hi && hi < 0xDC00 then
      if at! s (j + 6) != 92 || at! s (j + 7) != 117 then throw "expected '\\', a low surrogate"
      let lo ← hex4 s (j + 8)
      if !(0xDC00 ≤ lo && lo < 0xE000) then throw "lone surrogate"
      stringBody s (j + 12) (acc.push (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))))
    else if 0xDC00 ≤ hi && hi < 0xE000 then throw "lone surrogate"
    else stringBody s (j + 6) (acc.push (Char.ofNat hi))
  | _ => throw "bad escape"

def string (s : ByteArray) (i : Nat) : R (String × Nat) :=
  if at! s i == 34 && i < s.size then stringBody s (i + 1) "" else throw "expected '\"'"

def literal (s : ByteArray) (i : Nat) (word : List UInt8) (v : Value) : R (Value × Nat) :=
  if (List.range word.length).all (fun k => at! s (i + k) == word.getD k 0) && i + word.length ≤ s.size
  then .ok (v, i + word.length) else .error "invalid literal"

/-- The object of members collected in order, as `objInsert` member by member builds it. -/
def objectOf (ms : Array (String × Value)) : Value :=
  let keys := ms.map (·.1)
  let plain := ms.all (fun (k, _) => (arrayIndex? k).isNone) &&
    (keys.toList.foldl (fun (acc : Option (Std.HashSet String)) k => acc.bind fun set =>
      if set.contains k then none else some (set.insert k)) (some {})).isSome
  if plain then .obj 0 ms.toList
  else .obj 0 (ms.foldl (fun fs (k, v) => objInsert fs k v) [])

mutual
partial def value (s : ByteArray) (i : Nat) : R (Value × Nat) := do
  let i := skipWs s i
  if i ≥ s.size then throw "unexpected end"
  match at! s i with
  | 123 => object s (i + 1) #[]
  | 91 => array s (i + 1) #[]
  | 34 => do let (str, j) ← stringBody s (i + 1) ""; pure (.str str, j)
  | 116 => literal s i [116, 114, 117, 101] (.bool true)
  | 102 => literal s i [102, 97, 108, 115, 101] (.bool false)
  | 110 => literal s i [110, 117, 108, 108] .null
  | b => if b == 45 || isDigit b then number s i else throw s!"unexpected byte {b}"

partial def object (s : ByteArray) (i : Nat) (ms : Array (String × Value)) : R (Value × Nat) := do
  let i := skipWs s i
  if ms.isEmpty && at! s i == 125 && i < s.size then return (objectOf ms, i + 1)
  let (k, i) ← string s i
  let i := skipWs s i
  if at! s i != 58 || i ≥ s.size then throw "expected ':'"
  let (v, i) ← value s (i + 1)
  let i := skipWs s i
  let ms := ms.push (k, v)
  if i < s.size && at! s i == 44 then object s (i + 1) ms
  else if i < s.size && at! s i == 125 then return (objectOf ms, i + 1)
  else throw "expected ',' or '}'"

partial def array (s : ByteArray) (i : Nat) (xs : Array Value) : R (Value × Nat) := do
  let i := skipWs s i
  if xs.isEmpty && at! s i == 93 && i < s.size then return (.arr 0 [], i + 1)
  let (v, i) ← value s i
  let i := skipWs s i
  let xs := xs.push v
  if i < s.size && at! s i == 44 then array s (i + 1) xs
  else if i < s.size && at! s i == 93 then return (.arr 0 xs.toList, i + 1)
  else throw "expected ',' or ']'"
end

end Fast

/-- Parse JSON text (a leading byte-order mark is skipped, as the engine does). -/
def parse (text : String) : Except String Value :=
  let s := text.toUTF8
  let i := if s.size ≥ 3 && Fast.at! s 0 == 0xEF && Fast.at! s 1 == 0xBB && Fast.at! s 2 == 0xBF then 3 else 0
  match Fast.value s i with
  | .ok (v, j) =>
    if Fast.skipWs s j == s.size then .ok v else .error "the input is not JSON: trailing characters"
  | .error e => .error s!"the input is not JSON: {e}"

/-- The character parser the byte parser replaces, kept to check them against each other. -/
def charParse (text : String) : Except String Value :=
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

/-- A number as JSON: the shortest text reading back to the double nearest to it; a number beyond
the range of the doubles is `null`, as `JSON.stringify` writes an infinite one. -/
def number' (x : Rat) : String :=
  if Num.isFiniteDouble x then Num.jsNumberToString x else "null"

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

/-- The two parsers agree: both refuse, or both give values with the same text. -/
def sameParse (t : String) : Bool :=
  match parse t, charParse t with
  | .ok a, .ok b => write a == write b
  | .error _, .error _ => true
  | _, _ => false

#guard ["{\"a\":1,\"b\":[true,false,null,-0.5e3,12],\"c\":{\"x\":\"y\\n\\u00e9\\ud83d\\ude00\"}}",
  "{\"b\":1,\"a\":2,\"b\":3}", "{\"1\":1,\"x\":2,\"0\":3}", "[]", "{}", " [1, 2 , 3 ] ", "\"é – ü\"",
  "01", "1.", "-", "{\"a\" 1}", "[1,]", "tru", "\"\\ud800\"", "\"a\nb\"", "1e400", "0.1", "[\"\\/\"]",
  "{\"a\":{}}x", "nul", "\"\\u0041\""].all sameParse

end Exegra.Json
