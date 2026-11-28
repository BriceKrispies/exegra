/-
Numbers are exact rationals (`Rat`; owner decision 2026-11-27, WG-5683): a JSON number and a number
literal are the exact value of their decimal text (`ofDecimal`), and arithmetic on them is exact. No
floating-point type is used anywhere in the semantics.

What remains of IEEE 754 doubles is the text a number is written as: JavaScript's
`Number.prototype.toString()` of the double nearest to it (`jsNumberToString`), so that a number the
JavaScript shell or the Rust oracle reads back is the double nearest to the exact value, and an
integer or a short decimal is written as JavaScript writes it. The nearest double and its shortest
digits are computed exactly, in integer arithmetic.

`fmod` is the remainder of truncating division with the sign of the dividend (C's `fmod`, which is
Rust's and JavaScript's `%`), exact on rationals.
-/

namespace Exegra.Num

/-- Natural number from ASCII decimal digits. -/
def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- The exact value `±m · 10^e` of a decimal text. Magnitudes far outside the range of a double are
cut short before any large power is computed: above `10^330` the value is `±10^331` (written as
infinite, beyond every double), below `10^-360` it is `0`. -/
def ofDecimal (neg : Bool) (m : Nat) (e : Int) : Rat :=
  if m == 0 then 0
  else
    let digits : Int := (toString m).length
    let mag : Rat :=
      if digits + e > 330 then (10 ^ 331 : Nat)
      else if digits + e < -360 then 0
      else if e ≥ 0 then ((m * 10 ^ e.toNat : Nat) : Rat)
      else (m : Rat) / ((10 ^ (-e).toNat : Nat) : Rat)
    if neg then -mag else mag

/-- `x − trunc(x / y) · y`, the remainder with the sign of the dividend (`y ≠ 0`; `0` for `y = 0`,
which every caller excludes). -/
def fmod (x y : Rat) : Rat :=
  if y == 0 then 0 else
  let q := x / y
  let t : Int := if q < 0 then -((-q).floor) else q.floor
  x - (t : Rat) * y

/-- Is the number an integer of magnitude below 2^53? -/
def safeInteger? (x : Rat) : Option Int :=
  if x.den == 1 && x.num.natAbs < 9007199254740992 then some x.num else none

/-- Is the number an integer? -/
def isInteger (x : Rat) : Bool := x.den == 1

/-- `num / (den * 2^e)` as a pair of naturals. -/
private def scaled (num den : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (num, den * 2 ^ e.toNat) else (num * 2 ^ (-e).toNat, den)

/-- The double nearest to `num / den` (`num, den > 0`), ties to even, as `(q, e)` with value
`q · 2^e`; `none` when it is beyond the largest double (infinite). -/
def nearest (num den : Nat) : Option (Nat × Int) :=
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
  if e > 971 then none else some (q, e)

/-- The exact value `q · 2^e` as a pair `(num, den)`. -/
private def pairOf (q : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (q * 2 ^ e.toNat, 1) else (q, 2 ^ (-e).toNat)

/-- Is the number within the range of the doubles (its nearest double finite)? -/
def isFiniteDouble (x : Rat) : Bool :=
  x == 0 || (nearest x.num.natAbs x.den).isSome

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

/-- Shortest digits `s` (no trailing zeros) and exponent `n` with `0.s * 10^n` reading back to the
double `q · 2^e`. -/
def shortestDigits (q : Nat) (e : Int) : String × Int :=
  let (num, den) := pairOf q e
  let target := some (q, e)
  let rec search (p : Nat) (fuel : Nat) : String × Int :=
    let (s, n) := roundDigits num den p
    match fuel with
    | 0 => (toString s, n)
    | fuel + 1 =>
      let ex : Int := n - (p : Int)
      let back := if s == 0 then none
        else if ex ≥ 0 then nearest (s * 10 ^ ex.toNat) 1 else nearest s (10 ^ (-ex).toNat)
      if back == target then (toString s, n) else search (p + 1) fuel
  let (s, n) := search 1 17
  -- strip trailing zeros (they do not change the value)
  let cs := s.toList.reverse.dropWhile (· == '0') |>.reverse
  (String.ofList (if cs.isEmpty then ['0'] else cs), n)

private def zeros (k : Nat) : String := String.ofList (List.replicate k '0')

/-- JavaScript's `Number.prototype.toString()` of the double nearest to `x`. -/
def jsNumberToString (x : Rat) : String :=
  if x == 0 then "0"
  else match safeInteger? x with
  | some i => toString i
  | none =>
    let sign := if x < 0 then "-" else ""
    match nearest x.num.natAbs x.den with
    | none => sign ++ "Infinity"
    | some (q, e) =>
      let (num, den) := pairOf q e
      if den == 1 && num < 9007199254740992 then sign ++ toString num
      else
        let (s, n) := shortestDigits q e
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

#guard jsNumberToString ((1 : Rat) / 10 + 2 / 10) == "0.3"
#guard jsNumberToString ((1 : Rat) / 3) == "0.3333333333333333"
#guard jsNumberToString (ofDecimal false 1 (-7)) == "1e-7"
#guard jsNumberToString (ofDecimal true 15 (-1)) == "-1.5"
#guard jsNumberToString (ofDecimal false 1 21) == "1e+21"
#guard jsNumberToString (ofDecimal false 123456789012345678 3) == "123456789012345680000"
#guard jsNumberToString (9007199254740993 : Int) == "9007199254740992"
#guard jsNumberToString (ofDecimal false 1 400) == "Infinity"
#guard fmod (-7) 2 == -1 && fmod (55 / 10) 2 == 15 / 10

end Exegra.Num
