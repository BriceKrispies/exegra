import Exegra.Json

/-!
# Writing JSON fast

The definition of JSON output (`Exegra.Json.write`) builds the text of every value as its own
string and joins them at every level, and `quote` builds a one-character string per character.
`writeTo acc v` appends the text of `v` to `acc` instead, one character or literal at a time, so
the text is built once, in place. `writeTo_eq` proves `writeTo acc v = acc ++ write v`, so
`write' v = write v` (`write'_eq`).
-/

namespace Exegra.Impl.JsonOut

open Exegra Exegra.Json

/-- `acc ++ escape c`, pushing the character itself when it needs no escape. -/
def escapeTo (acc : String) (c : Char) : String :=
  if c == '"' || c == '\\' || c.toNat < 0x20 then acc ++ escape c else acc.push c

/-- `acc ++ quote s`. -/
def quoteTo (acc s : String) : String :=
  (s.foldl escapeTo (acc.push '"')).push '"'

mutual
/-- `acc ++ write v`. -/
def writeTo (acc : String) : Value → String
  | .undef => acc ++ "null"
  | .null => acc ++ "null"
  | .bool b => acc ++ (if b then "true" else "false")
  | .num x => acc ++ number' x
  | .str s => quoteTo acc s
  | .arr _ xs => (itemsTo (acc.push '[') true xs).push ']'
  | .obj _ fs => (membersTo (acc.push '{') true fs).push '}'

/-- The items of an array, separated by commas; `first` when none has been written yet. -/
def itemsTo (acc : String) (first : Bool) : List Value → String
  | [] => acc
  | x :: xs => itemsTo (writeTo (if first then acc else acc.push ',') x) false xs

/-- The members of an object that are not `undefined`, separated by commas. -/
def membersTo (acc : String) (first : Bool) : List (String × Value) → String
  | [] => acc
  | (k, v) :: fs =>
    match v with
    | .undef => membersTo acc first fs
    | _ => membersTo (writeTo ((quoteTo (if first then acc else acc.push ',') k).push ':') v) false fs
end

/-- Compact JSON text of a value, built in place. -/
def write' (v : Value) : String := writeTo "" v

/-! ## Agreement with the definition -/

theorem escapeTo_eq (acc : String) (c : Char) : escapeTo acc c = acc ++ escape c := by
  unfold escapeTo
  split
  · rfl
  · rename_i h
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e : escape c = c.toString := by
      unfold escape
      split <;> (try (exfalso; simp_all; done))
      simp only [show ¬ c.toNat < 0x20 by omega, ite_false]
    rw [e, String.push_eq_append]
    rfl

private theorem foldl_escape (l : List Char) (acc : String) :
    l.foldl (fun a c => a ++ escape c) acc = acc ++ l.foldl (fun a c => a ++ escape c) "" := by
  induction l generalizing acc with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih ("" ++ escape c)]
    simp [String.append_assoc]

private theorem foldl_escapeTo (l : List Char) (acc : String) :
    l.foldl escapeTo acc = acc ++ l.foldl (fun a c => a ++ escape c) "" := by
  have : escapeTo = fun a c => a ++ escape c := funext fun a => funext fun c => escapeTo_eq a c
  rw [this, foldl_escape]

theorem quoteTo_eq (acc s : String) : quoteTo acc s = acc ++ quote s := by
  unfold quoteTo quote
  rw [String.foldl_eq_foldl_toList, foldl_escapeTo, String.push_eq_append,
    String.push_eq_append]
  simp only [String.append_assoc]
  rfl

mutual
theorem writeTo_eq (acc : String) : (v : Value) → writeTo acc v = acc ++ write v
  | .undef => by simp [writeTo, write]
  | .null => by simp [writeTo, write]
  | .bool b => by simp [writeTo, write]
  | .num x => by simp [writeTo, write]
  | .str s => by simp [writeTo, write, quoteTo_eq]
  | .arr _ xs => by
    simp only [writeTo, write, String.push_eq_append, itemsTo_eq]
    cases h : writeItems xs <;> simp [String.append_assoc]
  | .obj _ fs => by
    simp only [writeTo, write, String.push_eq_append, membersTo_eq]
    cases h : writeMembers fs <;> simp [String.append_assoc]

/-- With `first`, the items' text; else a comma before each item. -/
theorem itemsTo_eq (acc : String) (first : Bool) : (xs : List Value) →
    itemsTo acc first xs =
      if first then acc ++ ",".intercalate (writeItems xs)
      else ",".intercalate (acc :: writeItems xs)
  | [] => by cases first <;> simp [itemsTo, writeItems]
  | x :: xs => by
    simp only [itemsTo, writeItems, Bool.false_eq_true, ite_false, itemsTo_eq _ false xs,
      writeTo_eq]
    cases first
    · simp only [Bool.false_eq_true, ite_false, String.push_eq_append]
      cases writeItems xs <;>
        simp [String.append_assoc, String.intercalate_cons_cons]
    · simp only [ite_true]
      cases writeItems xs <;>
        simp [String.append_assoc, String.intercalate_cons_cons]

theorem membersTo_eq (acc : String) (first : Bool) : (fs : List (String × Value)) →
    membersTo acc first fs =
      if first then acc ++ ",".intercalate (writeMembers fs)
      else ",".intercalate (acc :: writeMembers fs)
  | [] => by cases first <;> simp [membersTo, writeMembers]
  | (k, v) :: fs => by
    cases v with
    | undef => simp only [membersTo, writeMembers, membersTo_eq acc first fs]
    | _ =>
      simp only [membersTo, writeMembers, membersTo_eq _ false fs, writeTo_eq, quoteTo_eq,
        String.push_eq_append, Bool.false_eq_true, ite_false]
      cases first
      · simp only [Bool.false_eq_true, ite_false]
        cases writeMembers fs <;>
          simp [String.append_assoc, String.intercalate_cons_cons]
      · simp only [ite_true]
        cases writeMembers fs <;>
          simp [String.append_assoc, String.intercalate_cons_cons]
end

/-- **The fast writer writes the definition's text.** -/
theorem write'_eq (v : Value) : write' v = write v := by
  simp [write', writeTo_eq]

/-- info: 'Exegra.Impl.JsonOut.write'_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms write'_eq

end Exegra.Impl.JsonOut
