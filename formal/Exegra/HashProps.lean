import Exegra.Hash

/-!
# The semantic hash depends only on semantic content

Two theorems about `Exegra.Hash.semanticHash` (the definition; what runs, `semanticHash'`, is
equal to it by `semanticHash'_eq`):

- `semanticHash_perm`: the order of the top-level declarations does not change the hash. With
  `Exegra.Model.Model.semanticHash_presentation` (Exegra/ModelProps.lean) this covers everything
  `normalize` drops: source positions, JSON paths, owners and records of nested declarations,
  references, expressions and the effective meta-model are not part of the hash's input at all.
- `semanticHash_key_order`: reordering the members of objects, at every depth, in the vocabulary
  and in the data of every declaration, does not change the hash. Reordering is any function `f`
  on member lists that returns a permutation of its argument, applied to every object
  (`reorderAll`); the values must have distinct keys in every object (`NodupKeys`), which holds
  for every value the model derivation produces (it assigns members like JavaScript).

The work is in three facts: `keyLe` is a total order on strings (`keyLe_trans`, `keyLe_total`,
`keyLe_antisymm`, the last through `unitKey_inj`); sorting by it makes permutations with
distinct keys equal (`mergeSort_perm_eq`); and `sortKeys` only sees each object's members through
that sort (`sortKeys_obj_perm`).
-/

namespace Exegra.Hash

open Exegra

/-! ## The order -/

theorem lexLe_total : ∀ a b : List Nat, (lexLe a b || lexLe b a) = true
  | [], _ => by simp [lexLe]
  | _ :: _, [] => by simp [lexLe]
  | x :: xs, y :: ys => by
    have ih := lexLe_total xs ys
    simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
    rcases Nat.lt_trichotomy x y with h | rfl | h
    · exact Or.inl (Or.inl h)
    · rcases ih with h | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl h)

theorem lexLe_trans : ∀ a b c : List Nat, lexLe a b = true → lexLe b c = true → lexLe a c = true
  | [], _, _, _, _ => by simp [lexLe]
  | _ :: _, [], _, h, _ => by simp [lexLe] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLe] at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · omega
    · omega
    · omega
    · exact Or.inr ⟨rfl, lexLe_trans xs ys zs h₁ h₂⟩

theorem lexLe_antisymm : ∀ a b : List Nat, lexLe a b = true → lexLe b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [lexLe] at h
  | _ :: _, [], h, _ => by simp [lexLe] at h
  | x :: xs, y :: ys, h₁, h₂ => by
    simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
    rcases h₁ with h₁ | ⟨rfl, h₁⟩
    · omega
    · rcases h₂ with h₂ | ⟨_, h₂⟩
      · omega
      · rw [lexLe_antisymm xs ys h₁ h₂]

/-- Distinct characters have distinct keys. -/
theorem unitKey_inj {c d : Char} (h : unitKey c = unitKey d) : c = d := by
  have hc := c.valid
  have hd := d.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at hc hd
  unfold unitKey at h
  apply Char.ext
  apply UInt32.toNat_inj.mp
  split at h <;> split at h <;> (try split at h) <;> (try split at h) <;> omega

theorem map_unitKey_inj : ∀ {a b : List Char}, a.map unitKey = b.map unitKey → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [unitKey_inj h.1, map_unitKey_inj h.2]

theorem keyLe_total (a b : String) : (keyLe a b || keyLe b a) = true := lexLe_total _ _

theorem keyLe_trans (a b c : String) (h₁ : keyLe a b = true) (h₂ : keyLe b c = true) :
    keyLe a c = true :=
  lexLe_trans _ _ _ h₁ h₂

theorem keyLe_antisymm (a b : String) (h₁ : keyLe a b = true) (h₂ : keyLe b a = true) : a = b :=
  String.toList_injective (map_unitKey_inj (lexLe_antisymm _ _ h₁ h₂))

/-! ## Sorting by key -/

/-- In a list with distinct keys, two members with the same key are the same member. -/
theorem eq_of_fst_eq {β : Type} :
    ∀ {l : List (String × β)}, (l.map (·.1)).Nodup →
      ∀ {a b}, a ∈ l → b ∈ l → a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, hn, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, hab.symm⟩ hn.1
    · exact absurd ⟨a, ha, hab⟩ hn.1
    · exact eq_of_fst_eq hn.2 ha hb hab

/-- **Sorting by key makes permutations with distinct keys equal.** -/
theorem mergeSort_perm_eq {β : Type} {l₁ l₂ : List (String × β)} (hp : l₁.Perm l₂)
    (hn : (l₁.map (·.1)).Nodup) :
    l₁.mergeSort (fun a b => keyLe a.1 b.1) = l₂.mergeSort (fun a b => keyLe a.1 b.1) := by
  have trans : ∀ a b c : String × β, keyLe a.1 b.1 = true → keyLe b.1 c.1 = true →
      keyLe a.1 c.1 = true := fun a b c => keyLe_trans a.1 b.1 c.1
  have total : ∀ a b : String × β, (keyLe a.1 b.1 || keyLe b.1 a.1) = true :=
    fun a b => keyLe_total a.1 b.1
  apply List.Perm.eq_of_pairwise (le := fun a b => keyLe a.1 b.1 = true)
  · intro a b ha hb h₁ h₂
    have ha' : a ∈ l₁ := (List.mergeSort_perm l₁ _).subset ha
    have hb' : b ∈ l₁ := hp.symm.subset ((List.mergeSort_perm l₂ _).subset hb)
    exact eq_of_fst_eq hn ha' hb' (keyLe_antisymm _ _ h₁ h₂)
  · exact List.pairwise_mergeSort trans total l₁
  · exact List.pairwise_mergeSort trans total l₂
  · exact (List.mergeSort_perm l₁ _).trans (hp.trans (List.mergeSort_perm l₂ _).symm)

theorem sortMembers_eq_map : ∀ fs : List (String × Value),
    sortMembers fs = fs.map (fun kv => (kv.1, sortKeys kv.2))
  | [] => rfl
  | (k, v) :: fs => by simp [sortMembers, sortMembers_eq_map fs]

theorem sortItems_eq_map : ∀ xs : List Value, sortItems xs = xs.map sortKeys
  | [] => rfl
  | x :: xs => by simp [sortItems, sortItems_eq_map xs]

theorem sortMembers_keys (l : List (String × Value)) :
    (sortMembers l).map (·.1) = l.map (·.1) := by
  rw [sortMembers_eq_map, List.map_map]; rfl

/-- `sortKeys` sees an object's members only up to order, given distinct keys. -/
theorem sortKeys_obj_perm (i j : Nat) {l₁ l₂ : List (String × Value)}
    (hp : (sortMembers l₁).Perm (sortMembers l₂)) (hn : (l₂.map (·.1)).Nodup) :
    sortKeys (.obj i l₁) = sortKeys (.obj j l₂) := by
  simp only [sortKeys]
  rw [mergeSort_perm_eq hp.symm (by rw [sortMembers_keys]; exact hn)]

/-! ## Order of declarations -/

/-- **The order of the top-level declarations does not change the hash.** -/
theorem semanticHash_perm (sv vocab : Value) {top₁ top₂ : List Decl} (hp : top₁.Perm top₂)
    (hn : (top₁.map (·.1)).Nodup) :
    semanticHash sv vocab top₁ = semanticHash sv vocab top₂ := by
  unfold semanticHash normalize
  rw [mergeSort_perm_eq hp hn]

/-! ## Order of keys -/

mutual
/-- Every object's members, at every depth, reordered by `f`. -/
def reorderAll (f : List (String × Value) → List (String × Value)) : Value → Value
  | .obj i fs => .obj i (f (reorderMembers f fs))
  | .arr i xs => .arr i (reorderItems f xs)
  | v => v

def reorderMembers (f : List (String × Value) → List (String × Value)) :
    List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: fs => (k, reorderAll f v) :: reorderMembers f fs

def reorderItems (f : List (String × Value) → List (String × Value)) : List Value → List Value
  | [] => []
  | x :: xs => reorderAll f x :: reorderItems f xs
end

mutual
/-- Every object, at every depth, has distinct keys. -/
def NodupKeys : Value → Prop
  | .obj _ fs => (fs.map (·.1)).Nodup ∧ NodupKeysMembers fs
  | .arr _ xs => NodupKeysItems xs
  | _ => True

def NodupKeysMembers : List (String × Value) → Prop
  | [] => True
  | (_, v) :: fs => NodupKeys v ∧ NodupKeysMembers fs

def NodupKeysItems : List Value → Prop
  | [] => True
  | x :: xs => NodupKeys x ∧ NodupKeysItems xs
end

theorem reorderMembers_eq_map (f : List (String × Value) → List (String × Value)) :
    ∀ fs : List (String × Value), reorderMembers f fs = fs.map (fun kv => (kv.1, reorderAll f kv.2))
  | [] => rfl
  | (k, v) :: fs => by simp [reorderMembers, reorderMembers_eq_map f fs]

section
-- The members and items lemmas share a mutual block with the value lemma, which needs `hf`.
set_option linter.unusedSectionVars false
variable (f : List (String × Value) → List (String × Value)) (hf : ∀ l, (f l).Perm l)
include hf

omit hf in
theorem reorderMembers_keys (fs : List (String × Value)) :
    (reorderMembers f fs).map (·.1) = fs.map (·.1) := by
  rw [reorderMembers_eq_map, List.map_map]; rfl

mutual
theorem sortKeys_reorderAll : ∀ v : Value, NodupKeys v → sortKeys (reorderAll f v) = sortKeys v
  | .obj i fs, h => by
    simp only [NodupKeys] at h
    simp only [reorderAll]
    apply sortKeys_obj_perm
    · rw [← sortMembers_reorderMembers fs h.2]
      rw [sortMembers_eq_map, sortMembers_eq_map]
      exact (hf _).map _
    · exact h.1
  | .arr i xs, h => by
    simp only [NodupKeys] at h
    simp only [reorderAll, sortKeys, sortItems_reorderItems xs h]
  | .undef, _ => rfl
  | .null, _ => rfl
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .str _, _ => rfl

theorem sortMembers_reorderMembers : ∀ fs : List (String × Value), NodupKeysMembers fs →
    sortMembers (reorderMembers f fs) = sortMembers fs
  | [], _ => rfl
  | (k, v) :: fs, h => by
    simp only [NodupKeysMembers] at h
    simp only [reorderMembers, sortMembers, sortKeys_reorderAll v h.1,
      sortMembers_reorderMembers fs h.2]

theorem sortItems_reorderItems : ∀ xs : List Value, NodupKeysItems xs →
    sortItems (reorderItems f xs) = sortItems xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [NodupKeysItems] at h
    simp only [reorderItems, sortItems, sortKeys_reorderAll x h.1, sortItems_reorderItems xs h.2]
end

/-- A declaration's value in the normal form does not depend on the order of its data's keys. -/
theorem sortKeys_entityValue_reorder (kind : String) (d : Value) (h : NodupKeys d) :
    sortKeys (entityValue kind (reorderAll f d)) = sortKeys (entityValue kind d) := by
  cases d with
  | obj i fs =>
    simp only [NodupKeys] at h
    have hhas : objHas (f (reorderMembers f fs)) "kind" = objHas fs "kind" := by
      have h1 : objHas (f (reorderMembers f fs)) "kind" = objHas (reorderMembers f fs) "kind" := by
        unfold objHas
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, (hf _).subset hx, hp⟩,
          fun ⟨x, hx, hp⟩ => ⟨x, (hf _).symm.subset hx, hp⟩⟩
      rw [h1, reorderMembers_eq_map]
      unfold objHas
      rw [List.any_map]
      rfl
    have hsm : (sortMembers (f (reorderMembers f fs))).Perm (sortMembers fs) := by
      rw [← sortMembers_reorderMembers f hf fs h.2, sortMembers_eq_map, sortMembers_eq_map]
      exact (hf _).map _
    simp only [reorderAll, entityValue, hhas]
    split
    · exact sortKeys_obj_perm 0 0 hsm h.1
    · rename_i hk
      apply sortKeys_obj_perm
      · simp only [sortMembers]
        exact hsm.cons _
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, h.1⟩
        intro hm
        apply hk
        unfold objHas
        rw [List.any_eq_true]
        obtain ⟨x, hx, hx1⟩ := List.mem_map.mp hm
        exact ⟨x, hx, by simp only [hx1, beq_self_eq_true]⟩
  | arr i xs => rfl
  | undef => rfl
  | null => rfl
  | bool _ => rfl
  | num _ => rfl
  | str _ => rfl

/-- **The order of object keys does not change the hash**: reordering the members of every
object, at every depth, of the vocabulary and of every declaration's data. -/
theorem semanticHash_key_order (sv vocab : Value) (top : List Decl) (hv : NodupKeys vocab)
    (ht : ∀ d ∈ top, NodupKeys d.2.2) :
    semanticHash sv (reorderAll f vocab) (top.map fun d => (d.1, d.2.1, reorderAll f d.2.2)) =
      semanticHash sv vocab top := by
  unfold semanticHash normalize
  congr 2
  simp only [sortKeys, sortMembers, sortKeys_reorderAll f hf vocab hv]
  congr 4
  rw [← List.map_mergeSort (r := fun a b => keyLe a.1 b.1) (fun a _ b _ => rfl)]
  simp only [sortItems_eq_map, List.map_map]
  have key : ∀ d ∈ top.mergeSort (fun a b => keyLe a.1 b.1),
      (sortKeys ∘ (fun d : Decl => entityValue d.2.1 d.2.2) ∘
        fun d : Decl => (d.1, d.2.1, reorderAll f d.2.2)) d =
      (sortKeys ∘ fun d : Decl => entityValue d.2.1 d.2.2) d := fun d hd => by
    simp only [Function.comp]
    exact sortKeys_entityValue_reorder f hf d.2.1 d.2.2
      (ht d ((List.mergeSort_perm top _).subset hd))
  rw [List.map_congr_left key]

end

/-- info: 'Exegra.Hash.semanticHash_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semanticHash_perm

/-- info: 'Exegra.Hash.semanticHash_key_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semanticHash_key_order

end Exegra.Hash
