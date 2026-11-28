import Exegra.Lower.Pinned

/-!
# Distribution families lowered to engine distributions

`lowerDistribution` (formerly `src/core/distributions.js`): a family whose values are already in
base units (`{constant}`, `{uniform: {lo, hi}}`, `{exponential: {mean}}`, `{lognormal: {median,
p99} | {median, sigma}}`, `{empirical: {samples} | {quantiles}}`) to the engine's `fixed`,
`uniform` or `table` distribution, as the JSON value the engine input holds. Integer arithmetic
only, on the pinned tables of `Exegra.Lower.Pinned`; the refusals have the messages the
JavaScript lowering gave.
-/

namespace Exegra.Lower.Dist

open Exegra

/-- The pinned rows, parsed from the canonical text on first use. -/
def pinnedRows : Thunk (List Row) := Thunk.mk fun _ =>
  pinnedLines.map fun l =>
    match l.splitOn " " with
    | [u, e, n] => { u := u.toInt?.getD 0, qexp := e.toInt?.getD 0, qnorm := n.toInt?.getD 0 }
    | _ => default

/-- A JSON number for an integer the lowering bounded below `2^53` (exact as a double). -/
def numV (n : Int) : Value := .num (n : Rat)

/-- The engine input's `unitExponential` table, `[[0, 0], [u, Qexp(u)], ...]`, as decimal strings. -/
def unitExponentialTable : Value :=
  .arr 0 (.arr 0 [.str "0", .str "0"] ::
    pinnedRows.get.map fun r => .arr 0 [.str (toString r.u), .str (toString r.qexp)])

/-- JavaScript's `String(v)` of a JSON value. -/
def jsText (v : Value) : String := v.display

/-- Parse an exact non-negative decimal (`"0.59"`, `"12"`; no exponent) to `(num, den)`. -/
def decimalOf? (s : String) : Option (Int × Int) :=
  match s.splitOn "." with
  | [i] => if !i.isEmpty && i.all Char.isDigit then some (i.toNat!, 1) else none
  | [i, f] =>
    if !i.isEmpty && i.all Char.isDigit && !f.isEmpty && f.all Char.isDigit then
      some ((i ++ f).toNat!, (10 : Int) ^ f.length)
    else none
  | _ => none

/-- `exactDecimal(v)`: an exact non-negative decimal from a number or a string. -/
def exactDecimal (v : Value) : Except String (Int × Int) :=
  let s := jsText v
  match decimalOf? s with
  | some p => .ok p
  | none => .error s!"\"{s}\" is not an exact non-negative decimal."

/-- `BigInt(v)` for the values a distribution holds: an integer number, or a string of decimal
digits with an optional sign. -/
def bigIntOf (v : Value) : Except String Int :=
  match v with
  | .num x => match Num.safeInteger? x with
    | some n => .ok n
    | none => .error s!"The number {Num.jsNumberToString x} cannot be converted to a BigInt because it is not an integer"
  | .str s =>
    let t := s.trimAscii.toString
    match t.toInt? with
    | some n => if t.startsWith "+" then .error s!"Cannot convert {s} to a BigInt" else .ok n
    | none => if t.isEmpty then .ok 0 else .error s!"Cannot convert {s} to a BigInt"
  | v => .error s!"Cannot convert {jsText v} to a BigInt"

/-- A lowered value below `2^53`, or the lowering error. -/
def bounded (x : Int) (path : String) : Except String Int :=
  if x ≥ TWO53 then .error s!"Distribution \"{path}\" lowers to values of 2^53 base units or more."
  else .ok x

/-- `σ` at scale `S` of a log-normal: from `{median: M, p99: P}` or `{median, sigma}`. -/
def lognormalSigma (l : Value) (path : String) : Except String Int := do
  let get (k : String) : Value := match l with
    | .obj _ fs => (objGet? fs k).getD .undef
    | _ => .undef
  let sigma ← match get "p99" with
    | .undef => do
      let (n, d) ← exactDecimal (get "sigma")
      pure (floorDiv (n * S) d)
    | p99 => do
      let M ← bigIntOf (get "median")
      let P ← bigIntOf p99
      if M < 1 || P ≤ M || P > 1000000 * M then
        throw s!"Distribution \"{path}\" needs 1 ≤ median < p99 ≤ 10^6 · median."
      pure (floorDiv (lnFp (floorDiv (P * S) M) * S) Z99)
  if sigma > 8 * S then throw s!"Distribution \"{path}\" has sigma above 8."
  pure sigma

/-- The member `k` of an object value (`undefined` when absent). -/
def mem (v : Value) (k : String) : Value :=
  match v with
  | .obj _ fs => (objGet? fs k).getD .undef
  | _ => .undef

def hasMem (v : Value) (k : String) : Bool :=
  match v with
  | .obj _ fs => objHas fs k
  | _ => false

def itemsOf : Value → List Value
  | .arr _ xs => xs
  | _ => []

def isArr : Value → Bool
  | .arr .. => true
  | _ => false

def point (u x : Int) : Value := .arr 0 [numV u, numV x]

def table (pts : List Value) : Value := .obj 0 [("kind", .str "table"), ("points", .arr 0 pts)]

/-- The number of the first sample at or above rank `⌈u · n / 2^32⌉` (at least 1). -/
def rankAt (u n : Int) : Int :=
  let r := (u * n + TWO32 - 1) / TWO32
  if r < 1 then 1 else r

/-- Lower a family to an engine distribution (`fixed`, `uniform` or `table`). -/
def lowerDistribution (d : Value) (path : String) : Except String Value := do
  if hasMem d "constant" then
    let (n, den) ← exactDecimal (mem d "constant")
    if n % den != 0 then throw s!"Distribution \"{path}\" is not a whole number of base units."
    let v ← bounded (n / den) path
    return .obj 0 [("kind", .str "fixed"), ("value", numV v)]
  if hasMem d "uniform" then
    let u := mem d "uniform"
    let lo ← bigIntOf (mem u "lo")
    let hi ← bigIntOf (mem u "hi")
    if lo > hi then throw s!"Distribution \"{path}\" has lo above hi."
    let lo ← bounded lo path
    let hi ← bounded hi path
    return .obj 0 [("kind", .str "uniform"), ("lo", numV lo), ("hi", numV hi)]
  if hasMem d "exponential" then
    let (a, b) ← exactDecimal (mem (mem d "exponential") "mean")
    let pts ← pinnedRows.get.mapM fun r => do
      pure (point r.u (← bounded (roundHalfEven (a * r.qexp) (b * TWO64)) path))
    return table (point 0 0 :: pts)
  if hasMem d "lognormal" then
    let l := mem d "lognormal"
    let sigma ← lognormalSigma l path
    let (mn, md) ← exactDecimal (mem l "median")
    if mn % md != 0 then
      throw s!"Distribution \"{path}\" has a median that is not a whole number of base units."
    let M := mn / md
    let pts ← pinnedRows.get.mapM fun r => do
      let z := r.qnorm * 2 ^ 32
      pure (point r.u (← bounded (roundHalfEven (M * expFp (floorDiv (sigma * z) S)) S) path))
    return table (point 0 0 :: pts)
  if hasMem d "empirical" then
    let e := mem d "empirical"
    if isArr (mem e "samples") then
      let xs ← (itemsOf (mem e "samples")).mapM bigIntOf
      let s := xs.mergeSort (· ≤ ·)
      match s with
      | [] => throw s!"Distribution \"{path}\" has no samples."
      | s0 :: _ =>
        let n : Int := s.length
        let first ← bounded s0 path
        let pts ← grid.tail.mapM fun u => do
          pure (point u (← bounded (s.getD (rankAt u n - 1).toNat 0) path))
        return table (point 0 first :: pts)
    if isArr (mem e "quantiles") then
      let mut pts : List Value := []
      let mut us : List Int := []
      let mut prevU : Int := -1
      for q in itemsOf (mem e "quantiles") do
        let (pn, pd) ← exactDecimal (match q with | .arr _ (p :: _) => p | _ => .undef)
        let u := roundHalfEven (pn * TWO32) pd
        if u ≤ prevU then throw s!"Distribution \"{path}\" has two quantiles at the same table point."
        prevU := u
        let x ← bigIntOf (match q with | .arr _ (_ :: x :: _) => x | _ => .undef)
        let x ← bounded x path
        pts := pts ++ [point u x]
        us := us ++ [u]
      if us.head? != some 0 || us.getLast? != some TWO32 then
        throw s!"Distribution \"{path}\" must give quantiles from 0 to 1."
      return table pts
  throw s!"Distribution \"{path}\" has an unknown family."

/-! ## The reference outputs of docs/simulation.md ("Lowering distributions") -/

#guard expFp LN2 == 2 ^ 97
#guard lnFp (2 ^ 97) == LN2
#guard lnFp (roundHalfEven (271828182845904523536028747135266249775724709369995 * S) (10 ^ 50)) == S - 16
#guard grid.length == 1046
#guard [grid[1]!, grid[512]!, grid[1023]!, TWO32 - 2, TWO32].map qexp ==
  [18023200333324837, 12786308645202655660, 127863086452026556598, 396375568001282325453, 421948185291687636773]
#guard [grid[1]!, grid[512]!, grid[1023]!, TWO32 - 2, TWO32].map qnorm ==
  [-57134530012947273077, 0, 57134530012947273077, 112908024744873384702, 116914684648236608820]
#guard (lognormalSigma (.obj 0 [("median", .num 1000), ("p99", .num 4000)]) "d").toOption == some 47212867929608158508829714117

end Exegra.Lower.Dist
