/-
Exact conversions between decimal text and IEEE 754 doubles, and the double operations that
Lean's `Float` does not provide.

The engine reads numbers with correct rounding (serde_json with `float_roundtrip`, and Rust's
`str::parse::<f64>` for expression literals), and JavaScript's `JSON.parse` does too. Lean's own
`Float.ofScientific` is not guaranteed to round correctly, so decimal text is converted here
exactly: the value is held as a ratio of natural numbers and rounded once, half to even.

`%` on doubles is C's `fmod` in both Rust and JavaScript (the remainder of truncating division,
with the sign of the dividend, always exact). Lean's `Float` has no remainder, so `fmod` below
computes it exactly from the bit patterns.

`jsNumberToString` is JavaScript's `Number.prototype.toString()`: the shortest digits that read
back to the same double. The engine prints numbers this way in two messages only (the token of
an `Unexpected "<token>"` parse error, and the version of an unsupported input); traces are
compared as numbers, so the text written for a number in a trace only has to read back to the
same double.
-/

namespace Exegra.Num

/-- The sign, integer significand and binary exponent of a finite double: `|x| = m * 2^e`. -/
def decompose (x : Float) : Bool × Nat × Int :=
  let b := x.toBits.toNat
  let neg := b >>> 63 == 1
  let ex := (b >>> 52) &&& 0x7FF
  let frac := b &&& (2 ^ 52 - 1)
  if ex == 0 then (neg, frac, -1074) else (neg, frac + 2 ^ 52, (ex : Int) - 1075)

/-- `num / (den * 2^e)` as a pair of naturals. -/
private def scaled (num den : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (num, den * 2 ^ e.toNat) else (num * 2 ^ (-e).toNat, den)

/-- The double nearest to `num / den` (ties to even), negated when `neg`. `den` must be positive. -/
def ofRat (neg : Bool) (num den : Nat) : Float :=
  if num == 0 || den == 0 then (if neg then -0.0 else 0.0)
  else
    let e0 : Int := (num.log2 : Int) - (den.log2 : Int) - 52
    let e1 : Int :=
      let (n, d) := scaled num den e0
      if n / d ≥ 2 ^ 52 then e0 else e0 - 1
    let e2 : Int := if e1 < -1074 then -1074 else e1
    let (n, d) := scaled num den e2
    let q := n / d
    let r := n % d
    let q := if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q
    let (q, e) := if q == 2 ^ 53 then (2 ^ 52, e2 + 1) else (q, e2)
    let mag : Float := if e > 971 then Float.inf else (q.toUInt64.toFloat).scaleB e
    if neg then -mag else mag

/-- The double nearest to `m * 10^e`. Magnitudes far outside the double range are cut short
(to infinity or zero) before any large power is computed. -/
def ofDecimal (neg : Bool) (m : Nat) (e : Int) : Float :=
  if m == 0 then (if neg then -0.0 else 0.0)
  else
    let digits : Int := (toString m).length
    if digits + e > 330 then (if neg then -Float.inf else Float.inf)
    else if digits + e < -360 then (if neg then -0.0 else 0.0)
    else if e ≥ 0 then ofRat neg (m * 10 ^ e.toNat) 1
    else ofRat neg m (10 ^ (-e).toNat)

/-- Natural number from ASCII decimal digits. -/
def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- C's `fmod`, which is Rust's and JavaScript's `%` on doubles: `x - trunc(x / y) * y`,
computed exactly. -/
def fmod (x y : Float) : Float :=
  if x.isNaN || y.isNaN || x.isInf || y == 0 then Float.nan
  else if y.isInf then x
  else if x == 0 then x
  else
    let (nx, mx, ex) := decompose x
    let (_, my, ey) := decompose y
    let e := min ex ey
    let X := mx * 2 ^ (ex - e).toNat
    let Y := my * 2 ^ (ey - e).toNat
    let R := X % Y
    if e ≥ 0 then ofRat nx (R * 2 ^ e.toNat) 1 else ofRat nx R (2 ^ (-e).toNat)

/-- Is the double an integer of magnitude below 2^53 (printed as plain digits)? -/
def safeInteger? (x : Float) : Option Int :=
  if x.isFinite && x.abs < 9007199254740992.0 && x.floor == x then
    let n : Nat := x.abs.toUInt64.toNat
    some (if x < 0 then -(n : Int) else n)
  else none

/-- The decimal exponent `n` with `10^(n-1) ≤ num/den < 10^n` (num, den positive). -/
private def decExponent (num den : Nat) : Int :=
  if num ≥ den then
    ((toString (num / den)).length : Int)
  else
    -- smallest j ≥ 1 with num * 10^j ≥ den; then n = 1 - j
    let rec go (j : Nat) (fuel : Nat) : Int :=
      match fuel with
      | 0 => 1 - (j : Int)
      | fuel + 1 => if num * 10 ^ j ≥ den then 1 - (j : Int) else go (j + 1) fuel
    go 1 400

/-- The `p` significant digits nearest to `num/den` (ties to even), with the decimal exponent
`n` of `0.d1d2... * 10^n`. -/
private def roundDigits (num den : Nat) (p : Nat) : Nat × Int :=
  let n := decExponent num den
  let sh : Int := (p : Int) - n
  let (a, b) := if sh ≥ 0 then (num * 10 ^ sh.toNat, den) else (num, den * 10 ^ (-sh).toNat)
  let q := a / b
  let r := a % b
  let q := if 2 * r > b || (2 * r == b && q % 2 == 1) then q + 1 else q
  if q == 10 ^ p then (10 ^ (p - 1), n + 1) else (q, n)

/-- Shortest digits `s` (no trailing zeros) and exponent `n` with `0.s * 10^n` reading back to `x`
(finite, nonzero). -/
def shortestDigits (x : Float) : String × Int :=
  let (_, m, e) := decompose x
  let (num, den) := if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  let target := x.abs
  let rec search (p : Nat) (fuel : Nat) : String × Int :=
    let (s, n) := roundDigits num den p
    match fuel with
    | 0 => (toString s, n)
    | fuel + 1 =>
      let back := ofDecimal false s (n - (p : Int))
      if back == target then (toString s, n) else search (p + 1) fuel
  let (s, n) := search 1 17
  -- strip trailing zeros (they do not change the value)
  let cs := s.toList.reverse.dropWhile (· == '0') |>.reverse
  (String.ofList (if cs.isEmpty then ['0'] else cs), n)

private def zeros (k : Nat) : String := String.ofList (List.replicate k '0')

/-- JavaScript's `Number.prototype.toString()` for a double. -/
def jsNumberToString (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x > 0 then "Infinity" else "-Infinity")
  else if x == 0 then "0"
  else match safeInteger? x with
  | some i => toString i
  | none =>
    let sign := if x < 0 then "-" else ""
    let (s, n) := shortestDigits x
    let k : Int := s.length
    let body :=
      if k ≤ n && n ≤ 21 then s ++ zeros (n - k).toNat
      else if 0 < n && n ≤ 21 then
        String.ofList (s.toList.take n.toNat) ++ "." ++ String.ofList (s.toList.drop n.toNat)
      else if -6 < n && n ≤ 0 then "0." ++ zeros (-n).toNat ++ s
      else
        let ex := n - 1
        let exs := (if ex ≥ 0 then "+" else "-") ++ toString ex.natAbs
        if k == 1 then s ++ "e" ++ exs
        else String.ofList (s.toList.take 1) ++ "." ++ String.ofList (s.toList.drop 1) ++ "e" ++ exs
    sign ++ body

end Exegra.Num
