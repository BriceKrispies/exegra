import Exegra.Json

/-
What the version-2 engine input shares with the formats before it (`Exegra/Format2.lean` decodes the
whole input): a variable declaration, the occurrence a fault acts on, and the helpers that read the
fields of a JSON object with the engine's refusal messages. Format 1 is gone (WG-5681).
-/

namespace Exegra

structure VariableIn where
  name : String
  /-- `undef` when the input has no `initial`. -/
  initial : Value
  deriving Inhabited

inductive Occurrence where
  /-- No `occurrence`: every attempt. -/
  | any
  /-- A number: that attempt only. -/
  | exactly (n : Rat)
  /-- Present but not a number: `occurrence === attempt` never holds. -/
  | never
  deriving Inhabited

def Occurrence.matches : Occurrence → Nat → Bool
  | .any, _ => true
  | .exactly n, k => n == (↑k : Rat)
  | .never, _ => false

namespace Decode

abbrev R := Except String

def field (o : List (String × Value)) (key : String) : Value := (objGet? o key).getD .undef

def object (v : Value) (what : String) : R (List (String × Value)) :=
  match v with
  | .obj _ fs => .ok fs
  | _ => .error s!"{what} must be an object."

def string (o : List (String × Value)) (key what : String) : R String :=
  match field o key with
  | .str s => .ok s
  | _ => .error s!"{what}: \"{key}\" must be a string."

def number (o : List (String × Value)) (key what : String) : R Rat :=
  match field o key with
  | .num x => .ok x
  | _ => .error s!"{what}: \"{key}\" must be a number."

def array (o : List (String × Value)) (key what : String) : R (List Value) :=
  match field o key with
  | .arr _ xs => .ok xs
  | _ => .error s!"{what}: \"{key}\" must be an array."

/-- `Array.isArray(x) ? x : []`. -/
def arrayOrEmpty (o : List (String × Value)) (key : String) : List Value :=
  match field o key with
  | .arr _ xs => xs
  | _ => []

/-- `x ?? {}`. -/
def payloadOrEmpty (v : Value) : Value := if v.isNullish then .obj 0 [] else v

/-- Map with the element index, stopping at the first error. -/
def mapIdx {α β} (f : Nat → α → R β) (xs : List α) : R (List β) :=
  let rec go (i : Nat) : List α → R (List β)
    | [] => .ok []
    | x :: xs => do let y ← f i x; let ys ← go (i + 1) xs; pure (y :: ys)
  go 0 xs

end Decode

end Exegra
