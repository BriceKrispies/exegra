/-
Open arrival processes of format 2 (`docs/simulation.md`, "Workloads"): the schedule of arrival
instants of an open workload, constant or Poisson, over phases with constant rates or ramps,
repeated with a period, stopping at the horizon.

Everything here is a pure function of the declaration, the cursor and the unit-exponential
samples it is handed (`E i`, the `i`-th further sample at scale 2^-64), so `Format2.lean` decides
which draws those are and records them. Poisson instants invert the integrated rate exactly, with
integer square roots; there is no thinning and no rejection loop, so one instant takes one draw
per phase it looks at.
-/

namespace Exegra.Work

/-- A rate in instants per second: constant `num/den`, or a linear ramp from `n0/d0` at the
phase's start to `n1/d1` at its end. -/
inductive Rate where
  | const (num den : Nat)
  | ramp (n0 d0 n1 d1 : Nat)
  deriving Inhabited

/-- The rate at the start and at the end of the phase. -/
def Rate.ends : Rate → (Nat × Nat) × (Nat × Nat)
  | .const a b => ((a, b), (a, b))
  | .ramp a0 b0 a1 b1 => ((a0, b0), (a1, b1))

structure Phase where
  start : Nat
  stop : Nat
  rate : Rate
  deriving Inhabited

/-- Where a workload's schedule is: repetition, phase, and the next `j` (constant) or the time of
the last instant of this phase (Poisson). -/
structure Cursor where
  rep : Nat := 0
  phase : Nat := 0
  j : Nat := 0
  last : Option Nat := none
  done : Bool := false
  deriving Inhabited

/-- The integer square root, digit by digit from the highest bit. -/
def isqrtGo (n : Nat) : Nat → Nat → Nat
  | 0, r => if (r + 1) * (r + 1) ≤ n then r + 1 else r
  | k + 1, r =>
    let c := r + 2 ^ (k + 1)
    isqrtGo n k (if c * c ≤ n then c else r)

def isqrt (n : Nat) : Nat := isqrtGo n (Nat.log2 n / 2 + 1) 0

/-- `⌈√x⌉`: `isqrt(x − 1) + 1` for `x > 0`, and 0 for 0. -/
def ceilSqrt (x : Nat) : Nat := if x = 0 then 0 else isqrt (x - 1) + 1

def two64 : Nat := 18446744073709551616

/-- The Poisson interarrival `s` from a point `d` base units into a phase of length `L`, whose
rate runs from `a0/b0` to `a1/b1` per second, for a unit exponential sample `e` (scale 2^-64):
`s` solves `ρ·s + γ·s²/2 = E`, rounded to the nearest integer (half up); `none` when the mass left
in a falling ramp is below `E`. With `Rd = b0·b1·L·P`, `ρ = Rn/Rd` and `γ = Gn/Rd`, and the terms
brought to the denominator `K = Rd·2^64`: `A = Rn·2^64`, `C = |Gn|·2^64`,
`B = Rn²·2^128 ± 2·|Gn|·e·Rd·2^64`. -/
def interarrival (P L a0 b0 a1 b1 d e : Nat) : Option Nat :=
  let rd : Nat := b0 * b1 * L * P
  let gn : Int := (a1 * b0 : Int) - (a0 * b1 : Int)
  let rn : Nat := ((a0 * b1 * L : Int) + gn * d).toNat
  if gn = 0 then
    some ((2 * e * rd + two64 * rn) / (2 * two64 * rn))
  else
    let A := rn * two64
    let C := gn.natAbs * two64
    let sq := rn * rn * two64 * two64
    let m := 2 * gn.natAbs * e * rd * two64
    if gn > 0 then
      some ((C + isqrt (4 * (sq + m)) - 2 * A) / (2 * C))
    else if sq < m then none
    else some ((2 * A + C - ceilSqrt (4 * (sq - m))) / (2 * C))

/-- The next arrival instant from the cursor. Returns the instant's time (none: no more
arrivals), the next cursor and how many samples of `E` it used. `fuel` bounds the phases looked
at. -/
def nextTime (P horizon : Nat) (phases : List Phase) (period : Option Nat) (poisson : Bool)
    (E : Nat → Nat) : Nat → Cursor → Nat → Option Nat × Cursor × Nat
  | 0, c, used => (none, { c with done := true }, used)
  | fuel + 1, c, used =>
    if c.done then (none, c, used) else
    let advance (c : Cursor) : Cursor := { c with phase := c.phase + 1, j := 0, last := none }
    match phases[c.phase]? with
    | none =>
      match period with
      | some _ => nextTime P horizon phases period poisson E fuel
          { c with rep := c.rep + 1, phase := 0, j := 0, last := none } used
      | none => (none, { c with done := true }, used)
    | some ph =>
      let off := c.rep * period.getD 0
      let start := ph.start + off
      let stop := ph.stop + off
      if start ≥ horizon then (none, { c with done := true }, used) else
      let ((a0, b0), (a1, b1)) := ph.rate.ends
      if !poisson then
        if a0 = 0 then nextTime P horizon phases period poisson E fuel (advance c) used else
        let t := start + c.j * P * b0 / a0
        if t ≥ stop || t ≥ horizon then nextTime P horizon phases period poisson E fuel (advance c) used
        else (some t, { c with j := c.j + 1 }, used)
      else
        if a0 = 0 && a1 = 0 then nextTime P horizon phases period poisson E fuel (advance c) used else
        let base := c.last.getD start
        match interarrival P (ph.stop - ph.start) a0 b0 a1 b1 (base - start) (E used) with
        | none => nextTime P horizon phases period poisson E fuel (advance c) (used + 1)
        | some s =>
          let t := base + s
          if t ≥ stop || t ≥ horizon then
            nextTime P horizon phases period poisson E fuel (advance c) (used + 1)
          else (some t, { c with last := some t }, used + 1)

/-- The fuel of `nextTime`: enough to look at every phase of every repetition before the
horizon. -/
def fuelFor (horizon : Nat) (phases : List Phase) : Nat := (horizon + 2) * (phases.length + 2)

/-! ## Facts -/

/-- An instant is always before the horizon. -/
theorem nextTime_lt_horizon (P horizon : Nat) (phases : List Phase) (period : Option Nat)
    (poisson : Bool) (E : Nat → Nat) :
    ∀ (fuel : Nat) (c : Cursor) (used t : Nat),
      (nextTime P horizon phases period poisson E fuel c used).1 = some t → t < horizon := by
  intro fuel
  induction fuel with
  | zero => intro c used t h; simp [nextTime] at h
  | succ fuel ih =>
    intro c used t
    unfold nextTime
    repeat' (first | split | (dsimp only; done) | dsimp only [] at *)
    all_goals intro h
    all_goals first
      | exact ih _ _ _ h
      | (simp at h; done)
      | (simp at h; subst h; simp at *; omega)

#guard isqrt 0 = 0
#guard isqrt 1 = 1
#guard isqrt 15 = 3
#guard isqrt 16 = 4
#guard isqrt (2 ^ 200) = 2 ^ 100
#guard isqrt (2 ^ 200 - 1) = 2 ^ 100 - 1
#guard ceilSqrt 16 = 4
#guard ceilSqrt 17 = 5
-- Constant 1000/s in microseconds: instants 1000 us apart from the phase start.
#guard (nextTime 1000000 10000 [{ start := 0, stop := 5000, rate := .const 1000 1 }] none false
  (fun _ => 0) 100 { j := 3 } 0).1 = some 3000
-- E = 1 (2^64 at scale 2^-64) at 1000/s gives a 1000 us interarrival.
#guard interarrival 1000000 1000 1000 1 1000 1 0 two64 = some 1000

end Exegra.Work
