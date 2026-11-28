import Exegra.Value

/-!
# Lowering distributions to the engine's integer forms

The integer algorithms of docs/simulation.md ("Lowering distributions"), formerly
`src/core/distributions.js`: the fixed-point `exp_fp` and `ln_fp` at scale `2^96`, the pinned
quantile tables `Qexp` (unit-mean exponential) and `Qnorm` (standard normal) at scale `2^-64` on
the standard grid, and the families `constant`, `uniform`, `exponential`, `lognormal` and
`empirical` lowered to `fixed`, `uniform` and `table` distributions. Every step is integer
arithmetic on `Int`; no floating-point operation touches a value.

**The pinned tables.** Computing `Qnorm` on the 1,045 grid points takes a bisection of 68 steps
per point over a 192-bit series, which is too slow to repeat on every load of the WebAssembly
core. The tables are therefore held as their canonical text (`pinnedText`, the text whose SHA-256
the specification pins), parsed on first use, and the build checks that the text is exactly what
the algorithms compute (`pinnedText_computed`, a `#guard` over every grid point).

Loops that run until a series term reaches zero carry fuel far above the number of terms any
argument in range needs (`seriesFuel`); the fuel is never what ends them for the arguments the
lowering passes.
-/

namespace Exegra.Lower.Dist

/-- Scale of the fixed-point arithmetic, `2^96`. -/
def S : Int := 2 ^ 96
/-- `round(ln 2 · S)`. -/
def LN2 : Int := 54916777467707473351141471128
/-- `round(Φ⁻¹(0.99) · S)`. -/
def Z99 : Int := 184312267429221101812985515261
/-- Scale of the normal CDF evaluation, `2^192`, and its constants. -/
def W : Int := 2 ^ 192
def LN2_W : Int := 4350955369971217654477563090224794165364344896676135745070
def ISQ2PI_W : Int := 2504201280626952864894549311249338563268063356138482501337

def TWO32 : Int := 2 ^ 32
def TWO53 : Int := 2 ^ 53
def TWO64 : Int := 2 ^ 64

/-- More iterations than any series of this file needs for an argument in range. -/
def seriesFuel : Nat := 100000

/-- Floor division (`b > 0`): Lean's `Int` division rounds towards negative infinity for a
positive divisor. -/
def floorDiv (a b : Int) : Int := a / b

/-- `n / d` rounded half to even, `d > 0`. -/
def roundHalfEven (n d : Int) : Int :=
  let q := floorDiv n d
  let r2 := 2 * (n - q * d)
  if r2 > d then q + 1 else if r2 < d then q else if q % 2 == 0 then q else q + 1

/-- `x · 2^k`, rounded down for a negative `k`. -/
def shift (x k : Int) : Int :=
  if k ≥ 0 then x * 2 ^ k.toNat else floorDiv x (2 ^ (-k).toNat)

/-- `exp` at scale `scale`, with `ln 2` at that scale. -/
def expAt (x scale ln2 : Int) : Int :=
  let k := floorDiv x ln2
  let r := x - k * ln2
  let rec go : Nat → Int → Int → Int → Int
    | 0, _, s, _ => s
    | fuel + 1, t, s, n =>
      let s := s + t
      let n := n + 1
      let t := floorDiv (t * r) (n * scale)
      if t == 0 then s else go fuel t s n
  shift (go seriesFuel scale 0 0) k

/-- `exp_fp(x)` for `x` at scale `S`, of either sign. -/
def expFp (x : Int) : Int := expAt x S LN2

/-- The number of bits of a positive integer. -/
def bitLength (y : Int) : Int := (y.toNat.log2 + 1 : Nat)

/-- `ln_fp(y)` for `y > 0` at scale `S` (`0` for `y ≤ 0`, which no caller passes). -/
def lnFp (y : Int) : Int :=
  if y ≤ 0 then 0 else
  let k := bitLength y - 97
  let m := if k < 0 then y * 2 ^ (-k).toNat else y / 2 ^ k.toNat
  let s := floorDiv ((m - S) * S) (m + S)
  let s2 := floorDiv (s * s) S
  let rec go : Nat → Int → Int → Int → Int
    | 0, _, acc, _ => acc
    | fuel + 1, t, acc, j =>
      let acc := acc + floorDiv t (2 * j + 1)
      let j := j + 1
      let t := floorDiv (t * s2) S
      if t == 0 then acc else go fuel t acc j
  2 * go seriesFuel s 0 0 + k * LN2

/-- The standard grid: `k · 2^22` for `k = 0 … 1023`, `2^32 − 2^(32−j)` for `j = 11 … 31`, then
`2^32`. -/
def grid : List Int :=
  ((List.range 1024).map fun (k : Nat) => (k : Int) * 2 ^ 22) ++
  ((List.range 21).map fun (i : Nat) => TWO32 - (2 : Int) ^ (32 - (i + 11))) ++ [TWO32]

/-- `Qexp(u)`: the unit-mean exponential quantile at scale `2^-64`, for a grid point `u > 0`. -/
def qexp (u : Int) : Int :=
  let y := if u == TWO32 then 2 ^ 63 else (TWO32 - u) * TWO64
  roundHalfEven (-lnFp y) TWO32

/-- `Φ` at scale `W` of `x` at scale `W`. -/
def phiW (x : Int) : Int :=
  let a := if x < 0 then -x else x
  let a2 := floorDiv (a * a) W
  let rec go : Nat → Int → Int → Int → Int
    | 0, _, total, _ => total
    | fuel + 1, term, total, n =>
      let total := total + term
      let n := n + 1
      let term := floorDiv (term * a2) (W * (2 * n + 1))
      if term == 0 then total else go fuel term total n
  let total := go seriesFuel a 0 0
  let dens := floorDiv (ISQ2PI_W * expAt (-(floorDiv a2 2)) W LN2_W) W
  let half := floorDiv (dens * total) W
  if x ≥ 0 then W / 2 + half else W / 2 - half

/-- `Qnorm(u)`: the standard normal quantile at scale `2^-64`, for a grid point `u > 0`. -/
def qnorm (u : Int) : Int :=
  let pW := if u == TWO32 then W - 2 ^ 159 else u * 2 ^ 160
  let rec go : Nat → Int → Int → Int
    | 0, lo, _ => lo
    | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := floorDiv (lo + hi) 2
        if phiW ((2 * mid + 1) * 2 ^ 127) ≥ pW then go fuel lo mid else go fuel (mid + 1) hi
      else lo
  go 200 (-8 * TWO64) (8 * TWO64)

/-- One row of the pinned tables. -/
structure Row where
  u : Int
  qexp : Int
  qnorm : Int
  deriving Inhabited, BEq, Repr

/-- The pinned tables as the algorithms compute them, on the grid points `us` (the grid points
with `u > 0`). A function, not a constant, so that compiled code never computes it on load. -/
def computedTables (us : List Int := grid.tail) : List Row :=
  us.map fun u => { u, qexp := qexp u, qnorm := qnorm u }

/-- The canonical text of a table: one line `u qexp qnorm` per row. -/
def canonicalText (rows : List Row) : String :=
  String.join (rows.map fun r => s!"{r.u} {r.qexp} {r.qnorm}\n")

end Exegra.Lower.Dist
