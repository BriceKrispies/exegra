/-
Seeded randomness of format 2 (`docs/simulation.md`, "Randomness" and "Latency, timeouts and
timers"): SplitMix64 as a family of independent named streams, FNV-1a 64, `uniformInt`, sampling
of integer distribution tables and categorical choice.

A stream key is `k = mix64(seed XOR fnv1a64(name))`, and the `i`-th draw of a stream (from 0) is
`mix64(k + (i + 1) · γ)`, all mod 2^64, so each stream is Vigna's reference `splitmix64` seeded
with `k`. The `#guard` checks at the end pin the published reference outputs.
-/

namespace Exegra.Random

/-- The golden gamma of SplitMix64. -/
def gamma : UInt64 := 0x9E3779B97F4A7C15

/-- SplitMix64's output function (`mix64`, all mod 2^64). -/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- 64-bit FNV-1a over bytes. -/
def fnv1a64Bytes (bs : List UInt8) : UInt64 :=
  bs.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001B3) 0xCBF29CE484222325

/-- 64-bit FNV-1a over the UTF-8 bytes of a string. -/
def fnv1a64 (s : String) : UInt64 := fnv1a64Bytes s.toUTF8.toList

/-- The key of the stream `name` under `seed`. -/
def streamKey (seed : UInt64) (name : String) : UInt64 := mix64 (seed ^^^ fnv1a64 name)

/-- The `i`-th draw (from 0) of a stream with key `k`. -/
def drawAt (k : UInt64) (i : Nat) : UInt64 := mix64 (k + (i.toUInt64 + 1) * gamma)

/-- The `i`-th draw of the stream `name` under `seed`. -/
def draw (seed : UInt64) (name : String) (i : Nat) : UInt64 := drawAt (streamKey seed name) i

/-- Vigna's `splitmix64` seeded with `s`: its first `n` outputs. -/
def reference (s : UInt64) (n : Nat) : List UInt64 := (List.range n).map (drawAt s)

/-- Seed of run `r` of a set of runs with base seed `s`: the `r`-th output of SplitMix64
seeded with `s`. -/
def runSeed (s : UInt64) (r : Nat) : UInt64 := drawAt s r

/-- `uniformInt(lo, hi) = lo + ((r · (hi − lo + 1)) >> 64)`, the product exact. -/
def uniformInt (r : UInt64) (lo hi : Nat) : Nat := lo + (r.toNat * (hi - lo + 1)) / 2 ^ 64

/-- A drawn index into `n ≥ 1` values. -/
def index (r : UInt64) (n : Nat) : Nat := uniformInt r 0 (n - 1)

/-- Categorical choice with integer weights (`W = Σ w ≥ 1`): `v = uniformInt(0, W − 1)` and the
first `i` with `w_0 + … + w_i > v`. -/
def categorical (r : UInt64) (ws : List Nat) : Nat :=
  let v := uniformInt r 0 (ws.foldl (· + ·) 0 - 1)
  let rec go (i acc : Nat) : List Nat → Nat
    | [] => i
    | w :: rest => if acc + w > v then i else go (i + 1) (acc + w) rest
  go 0 0 ws

/-- Sample an integer table `[[u, x], ...]` (`u` strictly increasing from 0 to 2^32): with
`u* = r >> 32`, in the segment `u_i ≤ u* < u_{i+1}`,
`x_i + floor((u* − u_i) · (x_{i+1} − x_i) / (u_{i+1} − u_i))`. -/
def sampleTable (r : UInt64) (points : List (Nat × Nat)) : Nat :=
  let u := r.toNat / 2 ^ 32
  let rec go : List (Nat × Nat) → Nat
    | [] => 0
    | [(_, x)] => x
    | (u0, x0) :: (u1, x1) :: rest =>
      if u < u1 then x0 + (u - u0) * (x1 - x0) / (u1 - u0) else go ((u1, x1) :: rest)
  go points

/-! ## Facts -/

theorem uniformInt_ge (r : UInt64) (lo hi : Nat) : lo ≤ uniformInt r lo hi :=
  Nat.le_add_right _ _

/-- `uniformInt` stays in `[lo, hi]`. -/
theorem uniformInt_le (r : UInt64) (lo hi : Nat) (h : lo ≤ hi) : uniformInt r lo hi ≤ hi := by
  unfold uniformInt
  have hr : r.toNat < 2 ^ 64 := r.toNat_lt
  have : r.toNat * (hi - lo + 1) / 2 ^ 64 < hi - lo + 1 := by
    apply Nat.div_lt_of_lt_mul
    exact Nat.mul_lt_mul_of_pos_right hr (Nat.succ_pos _)
  omega

/-! ## Reference outputs -/

-- Vigna's `splitmix64.c` with seed 1234567, the published test vector.
#guard reference 1234567 5 =
  [6457827717110365317, 3203168211198807973, 9817491932198370423, 4593380528125082431,
   16408922859458223821]

-- FNV-1a 64 test vectors (empty string, "a", "foobar").
#guard fnv1a64 "" = 0xCBF29CE484222325
#guard fnv1a64 "a" = 0xAF63DC4C8601EC8C
#guard fnv1a64 "foobar" = 0x85944171F73967E8

-- A named stream: seed 42, stream `demand:db:t:0`.
#guard streamKey 42 "demand:db:t:0" = 6535567660793705486
#guard draw 42 "demand:db:t:0" 0 = 10373339710906660984

#guard uniformInt 0 3 7 = 3
#guard uniformInt 0xFFFFFFFFFFFFFFFF 3 7 = 7
#guard categorical 0 [0, 2, 1] = 1
#guard categorical 0xFFFFFFFFFFFFFFFF [0, 2, 1] = 2
#guard sampleTable 0 [(0, 10), (4294967296, 20)] = 10
#guard sampleTable 0x8000000000000000 [(0, 10), (4294967296, 20)] = 15
#guard sampleTable 0xFFFFFFFFFFFFFFFF [(0, 10), (4294967296, 20)] = 19

end Exegra.Random
