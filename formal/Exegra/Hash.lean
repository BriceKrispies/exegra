import Exegra.Json
import Exegra.Impl.Json

/-!
# The semantic hash of a specification

The normal form of a model and its 53-bit hash, as `src/core/hash.js` computed them before the
port (and as that file now asks the Lean core to compute them):

- `normalize`: the schema version, the vocabulary and the top-level declarations, each with its
  `kind`, sorted by id, with the keys of every object sorted. Source positions, JSON paths, the
  owner of nested declarations and the order of declarations are not part of it, and nested
  declarations appear only inside the data of the declaration that contains them.
- `cyrb53`: the 53-bit string hash cyrb53 over the UTF-16 code units of the compact JSON text of
  the normal form, written as 14 lower-case hexadecimal digits.

Bit-exactness with the JavaScript it replaces:

- keys are sorted the way `Array.prototype.sort` sorts strings, by UTF-16 code units
  (`keyLe`, through a per-character key that orders code points the way their UTF-16 encodings
  are ordered), and an object built from sorted keys keeps JavaScript's property order (canonical
  array-index keys first, ascending) because it is built with `objInsert`;
- `{kind, ...data}` and the sort only depend on the key-to-value map of the data, so
  `entityValue` puts `kind` in front unless the data has its own `kind`;
- `Math.imul`, `^` and `>>>` are 32-bit operations on the same bit patterns as `UInt32`
  multiplication, exclusive or and shift.

`semanticHash` is the definition (written with `Json.write`); `semanticHash'` is what runs: keys
converted once for sorting (`sortKeys'`) and the in-place writer. `semanticHash'_eq` proves them
equal. The theorems that the hash
depends only on semantic content are in `Exegra/HashProps.lean`.
-/

namespace Exegra.Hash

open Exegra

/-! ## String order by UTF-16 code units -/

/-- A number per character whose order is the order of the characters' UTF-16 encodings:
characters below the surrogate range come first, then the supplementary characters (encoded with
a high surrogate, 0xD800-0xDBFF), then the characters 0xE000-0xFFFF. -/
def unitKey (c : Char) : Nat :=
  if c.val.toNat < 0xD800 then c.val.toNat
  else if c.val.toNat < 0x10000 then c.val.toNat + 0x200000
  else c.val.toNat

/-- Lexicographic order of number lists, shorter prefix first. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && lexLe xs ys)

/-- `a ≤ b` in the order JavaScript sorts strings in (UTF-16 code units). -/
def keyLe (a b : String) : Bool := lexLe (a.toList.map unitKey) (b.toList.map unitKey)

/-! ## Normal form -/

/-- An object built from members in the given order, with JavaScript's assignment semantics. -/
def build (l : List (String × Value)) : List (String × Value) :=
  l.foldl (fun acc kv => objInsert acc kv.1 kv.2) []

mutual
/-- The value with the keys of every object sorted (`sortKeys` in hash.js). -/
def sortKeys : Value → Value
  | .arr _ xs => .arr 0 (sortItems xs)
  | .obj _ fs => .obj 0 (build ((sortMembers fs).mergeSort (fun a b => keyLe a.1 b.1)))
  | v => v

def sortItems : List Value → List Value
  | [] => []
  | x :: xs => sortKeys x :: sortItems xs

def sortMembers : List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: fs => (k, sortKeys v) :: sortMembers fs
end

/-- A declaration as the normal form lists it: `{kind, ...data}`. Only the key-to-value map of
the result matters (it is sorted next), so `kind` goes in front unless the data has its own. -/
def entityValue (kind : String) (data : Value) : Value :=
  match data with
  | .obj _ fs => .obj 0 (if objHas fs "kind" then fs else ("kind", .str kind) :: fs)
  | _ => .obj 0 [("kind", .str kind)]

/-- A top-level declaration: id, kind and data. -/
abbrev Decl := String × String × Value

/-- The normal form of a model: schema version, vocabulary and the top-level declarations sorted
by id, with every object's keys sorted. -/
def normalize (schemaVersion vocabulary : Value) (top : List Decl) : Value :=
  sortKeys (.obj 0 [
    ("schemaVersion", schemaVersion),
    ("vocabulary", vocabulary),
    ("entities", .arr 0 ((top.mergeSort (fun a b => keyLe a.1 b.1)).map
      (fun d => entityValue d.2.1 d.2.2)))])

/-! ## cyrb53 -/

/-- The UTF-16 code units of a character. -/
def units (c : Char) : List UInt32 :=
  if c.val < 0x10000 then [c.val]
  else
    let v := c.val - 0x10000
    [(0xD800 : UInt32) + (v >>> 10), (0xDC00 : UInt32) + (v &&& 0x3FF)]

/-- One code unit into the two halves of the state. -/
def mix (h : UInt32 × UInt32) (u : UInt32) : UInt32 × UInt32 :=
  ((h.1 ^^^ u) * 2654435761, (h.2 ^^^ u) * 1597334677)

/-- The state after every code unit of the text. -/
def absorb (s : String) : UInt32 × UInt32 :=
  s.foldl (fun h c => (units c).foldl mix h) (0xdeadbeef, 0x41c6ce57)

/-- `n` as lower-case hexadecimal, left-padded with zeros to `w` digits. -/
def hexPad (w n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (w - ds.length) '0' ++ ds)

/-- cyrb53 of a text (`hashString` in hash.js before the port): 14 hexadecimal digits. -/
def cyrb53 (s : String) : String :=
  let (h1, h2) := absorb s
  let h1' : UInt32 := ((h1 ^^^ (h1 >>> 16)) * (2246822507 : UInt32)) ^^^ ((h2 ^^^ (h2 >>> 13)) * (3266489909 : UInt32))
  let h2' : UInt32 := ((h2 ^^^ (h2 >>> 16)) * (2246822507 : UInt32)) ^^^ ((h1' ^^^ (h1' >>> 13)) * (3266489909 : UInt32))
  hexPad 14 (4294967296 * ((2097151 : UInt32) &&& h2').toNat + h1'.toNat)

/-- **The semantic hash** (definition): cyrb53 of the JSON text of the normal form. -/
def semanticHash (schemaVersion vocabulary : Value) (top : List Decl) : String :=
  cyrb53 (Json.write (normalize schemaVersion vocabulary top))

/-! ## The implementation that runs

`sortKeys` compares keys with `keyLe`, which converts both strings at every comparison of the
merge sort. `sortKeys'` converts each key once (`decorate`), sorts the pairs by the converted keys
and drops them again; `sortKeys'_eq` proves it equal to `sortKeys`. `semanticHash'` uses it and
writes the normal form with the in-place writer (`Impl.JsonOut.write'_eq`). -/

/-- A member with its key converted for comparison. -/
def decorate (kv : String × Value) : List Nat × (String × Value) := (kv.1.toList.map unitKey, kv)

/-- `l.mergeSort (keyLe on keys)`, converting each key once. -/
def sortByKey (l : List (String × Value)) : List (String × Value) :=
  ((l.map decorate).mergeSort (fun a b => lexLe a.1 b.1)).map (·.2)

theorem sortByKey_eq (l : List (String × Value)) :
    sortByKey l = l.mergeSort (fun a b => keyLe a.1 b.1) := by
  unfold sortByKey
  rw [← List.map_mergeSort (r := fun a b => keyLe a.1 b.1) (fun a _ b _ => rfl)]
  rw [List.map_map]
  have : ((fun x : List Nat × (String × Value) => x.snd) ∘ decorate) = id := rfl
  rw [this, List.map_id]

mutual
def sortKeys' : Value → Value
  | .arr _ xs => .arr 0 (sortItems' xs)
  | .obj _ fs => .obj 0 (build (sortByKey (sortMembers' fs)))
  | v => v

def sortItems' : List Value → List Value
  | [] => []
  | x :: xs => sortKeys' x :: sortItems' xs

def sortMembers' : List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: fs => (k, sortKeys' v) :: sortMembers' fs
end

mutual
theorem sortKeys'_eq : (v : Value) → sortKeys' v = sortKeys v
  | .arr _ xs => by simp only [sortKeys', sortKeys, sortItems'_eq xs]
  | .obj _ fs => by simp only [sortKeys', sortKeys, sortMembers'_eq fs, sortByKey_eq]
  | .undef => rfl
  | .null => rfl
  | .bool _ => rfl
  | .num _ => rfl
  | .str _ => rfl

theorem sortItems'_eq : (xs : List Value) → sortItems' xs = sortItems xs
  | [] => rfl
  | x :: xs => by simp only [sortItems', sortItems, sortKeys'_eq x, sortItems'_eq xs]

theorem sortMembers'_eq : (fs : List (String × Value)) → sortMembers' fs = sortMembers fs
  | [] => rfl
  | (k, v) :: fs => by simp only [sortMembers', sortMembers, sortKeys'_eq v, sortMembers'_eq fs]
end

/-- A declaration with its id converted for comparison. -/
def decorateDecl (d : Decl) : List Nat × Decl := (d.1.toList.map unitKey, d)

/-- The normal form as it runs: keys and ids converted once for sorting. -/
def normalize' (schemaVersion vocabulary : Value) (top : List Decl) : Value :=
  sortKeys' (.obj 0 [
    ("schemaVersion", schemaVersion),
    ("vocabulary", vocabulary),
    ("entities", .arr 0 ((((top.map decorateDecl).mergeSort (fun a b => lexLe a.1 b.1)).map (·.2)).map
      (fun d => entityValue d.2.1 d.2.2)))])

theorem normalize'_eq (sv vocab : Value) (top : List Decl) :
    normalize' sv vocab top = normalize sv vocab top := by
  unfold normalize' normalize
  rw [sortKeys'_eq]
  congr
  rw [← List.map_mergeSort (r := fun a b => keyLe a.1 b.1) (fun a _ b _ => rfl)]
  rw [List.map_map]
  have : ((fun x : List Nat × Decl => x.snd) ∘ decorateDecl) = id := rfl
  rw [this, List.map_id]

/-- The semantic hash as it runs. -/
def semanticHash' (schemaVersion vocabulary : Value) (top : List Decl) : String :=
  cyrb53 (Impl.JsonOut.write' (normalize' schemaVersion vocabulary top))

/-- **The hash that runs is the definition.** -/
theorem semanticHash'_eq (sv vocab : Value) (top : List Decl) :
    semanticHash' sv vocab top = semanticHash sv vocab top := by
  simp [semanticHash', semanticHash, Impl.JsonOut.write'_eq, normalize'_eq]

/-- info: 'Exegra.Hash.semanticHash'_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semanticHash'_eq

end Exegra.Hash
