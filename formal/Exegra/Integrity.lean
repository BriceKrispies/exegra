import Exegra.Json

/-
Integrity rules over a finite specification, decided in the kernel.

A rule of `src/core/integrity.js` is exported (`src/core/integrity-export.js`) as a `Formula` over
`Facts`: the entities the rule can reach, each with its kind and the values of only the properties
the rule reads. Every string (ids, kinds, property names, literals) is interned to a `Nat`, so the
kernel compares numbers (`Nat.beq`, `Nat.blt`, which it evaluates natively) and never strings.
Facts are a binary search tree keyed by entity id, so following a reference is a logarithmic walk.

* `Sat u env φ` is the meaning of a formula, as a `Prop`.
* `eval u env φ` is a Bool checker by structural recursion, so the kernel can evaluate it.
* `eval_iff` proves the two agree. A rule that holds is then proved by reflection:
  `holds_of_eval (by decide +kernel)`, with no axiom beyond Lean's standard ones.
* `refutes u env φ w` checks one witness: values for the leading universal quantifiers that
  are in range, pass the filters, and falsify the body. `refutes_sound` proves that such a witness
  refutes the rule, so a violation is proved from the concrete counterexample alone.
* `cex` lists every witness; `exegra-lean integrity` runs it for the differential test against the
  JavaScript evaluator.
-/

namespace Exegra.Integrity

/-- One entity: interned id, interned kind, and the (property, values) pairs a rule reads. -/
structure Ent where
  id : Nat
  kind : Nat
  props : List (Nat × List Nat)
  deriving Inhabited

inductive Facts where
  | leaf
  | node (l : Facts) (e : Ent) (r : Facts)
  deriving Inhabited

namespace Facts

def Mem (x : Ent) : Facts → Prop
  | .leaf => False
  | .node l e r => x = e ∨ Mem x l ∨ Mem x r

def find : Facts → Nat → Option Ent
  | .leaf, _ => none
  | .node l e r, x => if Nat.beq x e.id then some e else if Nat.blt x e.id then find l x else find r x

def all (p : Ent → Bool) : Facts → Bool
  | .leaf => true
  | .node l e r => p e && all p l && all p r

def toList : Facts → List Ent
  | .leaf => []
  | .node l e r => toList l ++ e :: toList r

/-- Keys strictly between `lo` and `hi` (exclusive, when given): a search tree. -/
def bst (lo hi : Option Nat) : Facts → Bool
  | .leaf => true
  | .node l e r =>
    (match lo with | some a => Nat.blt a e.id | none => true) &&
    (match hi with | some b => Nat.blt e.id b | none => true) &&
    bst lo (some e.id) l && bst (some e.id) hi r

theorem all_iff (p : Ent → Bool) : ∀ t : Facts, t.all p = true ↔ ∀ e, t.Mem e → p e = true
  | .leaf => by simp [all, Mem]
  | .node l e r => by
    have hl := all_iff p l
    have hr := all_iff p r
    simp only [all, Mem, Bool.and_eq_true, hl, hr]
    constructor
    · rintro ⟨⟨he, h1⟩, h2⟩ x hx
      rcases hx with rfl | hx | hx
      · exact he
      · exact h1 x hx
      · exact h2 x hx
    · intro h
      exact ⟨⟨h e (Or.inl rfl), fun x hx => h x (Or.inr (Or.inl hx))⟩, fun x hx => h x (Or.inr (Or.inr hx))⟩

theorem find_sound : ∀ (t : Facts) (x : Nat) (e : Ent), t.find x = some e → t.Mem e ∧ e.id = x
  | .leaf, _, _, h => by simp [find] at h
  | .node l c r, x, e, h => by
    simp only [find] at h
    split at h
    · rename_i hb
      cases h
      exact ⟨Or.inl rfl, (Nat.eq_of_beq_eq_true hb).symm⟩
    · split at h
      · have := find_sound l x e h
        exact ⟨Or.inr (Or.inl this.1), this.2⟩
      · have := find_sound r x e h
        exact ⟨Or.inr (Or.inr this.1), this.2⟩

theorem bst_bounds : ∀ (t : Facts) (lo hi : Option Nat), bst lo hi t = true → ∀ e, t.Mem e →
    (∀ a, lo = some a → a < e.id) ∧ (∀ b, hi = some b → e.id < b)
  | .leaf, _, _, _, _, h => by simp [Mem] at h
  | .node l c r, lo, hi, h, e, hm => by
    simp only [bst, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hlo, hhi⟩, hl⟩, hr⟩ := h
    have clo : ∀ a, lo = some a → a < c.id := by
      intro a ha; subst ha; simpa [Nat.blt_eq] using hlo
    have chi : ∀ b, hi = some b → c.id < b := by
      intro b hb; subst hb; simpa [Nat.blt_eq] using hhi
    rcases hm with rfl | hm | hm
    · exact ⟨clo, chi⟩
    · have ⟨h1, h2⟩ := bst_bounds l lo (some c.id) hl e hm
      exact ⟨h1, fun b hb => Nat.lt_trans (h2 c.id rfl) (chi b hb)⟩
    · have ⟨h1, h2⟩ := bst_bounds r (some c.id) hi hr e hm
      exact ⟨fun a ha => Nat.lt_trans (clo a ha) (h1 c.id rfl), h2⟩

/-- In a search tree, `find` returns every entity that is in the tree, by its id: following a
reference sees exactly the entity the facts hold under that id. -/
theorem find_complete : ∀ (t : Facts) (lo hi : Option Nat), bst lo hi t = true → ∀ e, t.Mem e →
    t.find e.id = some e
  | .leaf, _, _, _, _, h => by simp [Mem] at h
  | .node l c r, lo, hi, h, e, hm => by
    have hall := h
    simp only [bst, Bool.and_eq_true] at h
    obtain ⟨⟨_, hl⟩, hr⟩ := h
    simp only [find]
    rcases hm with rfl | hm | hm
    · simp
    · have ⟨_, h2⟩ := bst_bounds l lo (some c.id) hl e hm
      have hlt := h2 c.id rfl
      have hne : Nat.beq e.id c.id = false := by
        cases h : Nat.beq e.id c.id
        · rfl
        · have := Nat.eq_of_beq_eq_true h; omega
      have hb : Nat.blt e.id c.id = true := by simpa [Nat.blt_eq] using hlt
      simp only [hne, hb, Bool.false_eq_true, ite_false, ite_true]
      exact find_complete l lo (some c.id) hl e hm
    · have ⟨h1, _⟩ := bst_bounds r (some c.id) hi hr e hm
      have hlt := h1 c.id rfl
      have hne : Nat.beq e.id c.id = false := by
        cases h : Nat.beq e.id c.id
        · rfl
        · have := Nat.eq_of_beq_eq_true h; omega
      have hnlt : Nat.blt e.id c.id = false := by
        cases h : Nat.blt e.id c.id
        · rfl
        · have : e.id < c.id := by simpa [Nat.blt_eq] using h
          omega
      simp only [hne, hnlt, Bool.false_eq_true, ite_false]
      exact find_complete r (some c.id) hi hr e hm

end Facts

/-! ## Lists of values -/

def memN (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => Nat.beq x y || memN x ys

theorem memN_iff (x : Nat) : ∀ l : List Nat, memN x l = true ↔ x ∈ l
  | [] => by simp [memN]
  | y :: ys => by
    simp only [memN, Bool.or_eq_true, memN_iff x ys, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl (Nat.eq_of_beq_eq_true h)
      · exact Or.inr h
    · rintro (h | h)
      · subst h; exact Or.inl (Nat.beq_refl x)
      · exact Or.inr h

def allL (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | x :: xs => p x && allL p xs

theorem allL_iff (p : Nat → Bool) : ∀ l : List Nat, allL p l = true ↔ ∀ x ∈ l, p x = true
  | [] => by simp [allL]
  | x :: xs => by simp [allL, allL_iff p xs]

def anyL (p : Nat → Bool) : List Nat → Bool
  | [] => false
  | x :: xs => p x || anyL p xs

theorem anyL_iff (p : Nat → Bool) : ∀ l : List Nat, anyL p l = true ↔ ∃ x ∈ l, p x = true
  | [] => by simp [anyL]
  | x :: xs => by simp [anyL, anyL_iff p xs]

def nonNil : List Nat → Bool
  | [] => false
  | _ :: _ => true

theorem nonNil_iff : ∀ l : List Nat, nonNil l = true ↔ l ≠ []
  | [] => by simp [nonNil]
  | _ :: _ => by simp [nonNil]

/-- The value of property `p` in a property list (the first entry for `p`; the export writes one). -/
def getProp (p : Nat) : List (Nat × List Nat) → List Nat
  | [] => []
  | (q, vs) :: rest => if Nat.beq p q then vs else getProp p rest

def nth : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

def flat (f : Nat → List Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => f x ++ flat f xs

/-! ## Terms and formulas -/

/-- A term denotes a finite list of values. -/
inductive Term where
  /-- A bound variable, by de Bruijn index (0 is the innermost quantifier). -/
  | var (i : Nat)
  /-- A literal: one value, or a literal set. -/
  | lit (vs : List Nat)
  /-- Property `p` of every value of `t` that is an entity id; nothing for other values. -/
  | prop (t : Term) (p : Nat)
  /-- The kind of every value of `t` that is an entity id. -/
  | kindOf (t : Term)

def evalTerm (u : Facts) (env : List Nat) : Term → List Nat
  | .var i => match nth env i with | some v => [v] | none => []
  | .lit vs => vs
  | .prop t p => flat (fun v => match u.find v with | some e => getProp p e.props | none => []) (evalTerm u env t)
  | .kindOf t => flat (fun v => match u.find v with | some e => [e.kind] | none => []) (evalTerm u env t)

/-- What a quantifier ranges over: every entity, the entities of some kinds, or a term's values. -/
inductive Dom where
  | any
  | kinds (ks : List Nat)
  | term (t : Term)

inductive Formula where
  | tt
  | ff
  | eq (a b : Term)
  | mem (a b : Term)
  | nonempty (a : Term)
  | not (f : Formula)
  | and (f g : Formula)
  | or (f g : Formula)
  | imp (f g : Formula)
  /-- `all d f b`: for every value `v` in `d` for which the filter `f` holds, `b` holds. -/
  | all (d : Dom) (f b : Formula)
  /-- `ex d f b`: some value `v` in `d` satisfies the filter `f` and `b`. -/
  | ex (d : Dom) (f b : Formula)

def InDom (u : Facts) (env : List Nat) : Dom → Nat → Prop
  | .any, v => ∃ e, u.Mem e ∧ e.id = v
  | .kinds ks, v => ∃ e, u.Mem e ∧ e.id = v ∧ e.kind ∈ ks
  | .term t, v => v ∈ evalTerm u env t

/-- The meaning of a formula. -/
def Sat (u : Facts) : List Nat → Formula → Prop
  | _, .tt => True
  | _, .ff => False
  | env, .eq a b => (∀ x ∈ evalTerm u env a, x ∈ evalTerm u env b) ∧ (∀ x ∈ evalTerm u env b, x ∈ evalTerm u env a)
  | env, .mem a b => evalTerm u env a ≠ [] ∧ ∀ x ∈ evalTerm u env a, x ∈ evalTerm u env b
  | env, .nonempty a => evalTerm u env a ≠ []
  | env, .not f => ¬ Sat u env f
  | env, .and f g => Sat u env f ∧ Sat u env g
  | env, .or f g => Sat u env f ∨ Sat u env g
  | env, .imp f g => Sat u env f → Sat u env g
  | env, .all d f b => ∀ v, InDom u env d v → Sat u (v :: env) f → Sat u (v :: env) b
  | env, .ex d f b => ∃ v, InDom u env d v ∧ Sat u (v :: env) f ∧ Sat u (v :: env) b

/-- Every value of `d` satisfies `p`. -/
def domAll (u : Facts) (env : List Nat) (d : Dom) (p : Nat → Bool) : Bool :=
  match d with
  | .any => u.all (fun e => p e.id)
  | .kinds ks => u.all (fun e => !memN e.kind ks || p e.id)
  | .term t => allL p (evalTerm u env t)

/-- Some value of `d` satisfies `p`. -/
def domAny (u : Facts) (env : List Nat) (d : Dom) (p : Nat → Bool) : Bool :=
  !domAll u env d (fun v => !p v)

def eval (u : Facts) : List Nat → Formula → Bool
  | _, .tt => true
  | _, .ff => false
  | env, .eq a b =>
    allL (fun x => memN x (evalTerm u env b)) (evalTerm u env a) &&
    allL (fun x => memN x (evalTerm u env a)) (evalTerm u env b)
  | env, .mem a b => nonNil (evalTerm u env a) && allL (fun x => memN x (evalTerm u env b)) (evalTerm u env a)
  | env, .nonempty a => nonNil (evalTerm u env a)
  | env, .not f => !eval u env f
  | env, .and f g => eval u env f && eval u env g
  | env, .or f g => eval u env f || eval u env g
  | env, .imp f g => !eval u env f || eval u env g
  | env, .all d f b => domAll u env d (fun v => !eval u (v :: env) f || eval u (v :: env) b)
  | env, .ex d f b => domAny u env d (fun v => eval u (v :: env) f && eval u (v :: env) b)

theorem domAll_iff (u : Facts) (env : List Nat) (d : Dom) (p : Nat → Bool) :
    domAll u env d p = true ↔ ∀ v, InDom u env d v → p v = true := by
  cases d with
  | any =>
    simp only [domAll, Facts.all_iff, InDom]
    constructor
    · rintro h v ⟨e, he, rfl⟩; exact h e he
    · intro h e he; exact h e.id ⟨e, he, rfl⟩
  | kinds ks =>
    simp only [domAll, Facts.all_iff, InDom, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · rintro h v ⟨e, he, rfl, hk⟩
      rcases h e he with h | h
      · rw [← Bool.not_eq_true, memN_iff] at h; exact absurd hk h
      · exact h
    · intro h e he
      by_cases hk : e.kind ∈ ks
      · exact Or.inr (h e.id ⟨e, he, rfl, hk⟩)
      · left; rw [← Bool.not_eq_true, memN_iff]; exact hk
  | term t => simp only [domAll, allL_iff, InDom]

theorem eval_iff (u : Facts) : ∀ (φ : Formula) (env : List Nat), eval u env φ = true ↔ Sat u env φ
  | .tt, _ => by simp [eval, Sat]
  | .ff, _ => by simp [eval, Sat]
  | .eq a b, env => by simp [eval, Sat, allL_iff, memN_iff]
  | .mem a b, env => by simp [eval, Sat, allL_iff, memN_iff, nonNil_iff]
  | .nonempty a, env => by simp [eval, Sat, nonNil_iff]
  | .not f, env => by simp [eval, Sat, ← eval_iff u f env]
  | .and f g, env => by simp [eval, Sat, eval_iff u f env, eval_iff u g env]
  | .or f g, env => by simp [eval, Sat, eval_iff u f env, eval_iff u g env]
  | .imp f g, env => by
    simp only [eval, Sat, Bool.or_eq_true, Bool.not_eq_true', ← eval_iff u f env, ← eval_iff u g env]
    cases eval u env f <;> simp
  | .all d f b, env => by
    simp only [eval, Sat, domAll_iff]
    apply forall_congr'; intro v; apply imp_congr_right; intro _
    rw [← eval_iff u f (v :: env), ← eval_iff u b (v :: env)]
    cases eval u (v :: env) f <;> simp
  | .ex d f b, env => by
    have key : ∀ v, (eval u (v :: env) f && eval u (v :: env) b) = true ↔
        Sat u (v :: env) f ∧ Sat u (v :: env) b := by
      intro v; rw [Bool.and_eq_true, eval_iff u f, eval_iff u b]
    simp only [eval, Sat, domAny, Bool.not_eq_true']
    constructor
    · intro h
      apply Classical.byContradiction; intro hn
      have : domAll u env d (fun v => !(eval u (v :: env) f && eval u (v :: env) b)) = true := by
        rw [domAll_iff]; intro v hv
        cases hx : (eval u (v :: env) f && eval u (v :: env) b)
        · rfl
        · exact absurd ⟨v, hv, (key v).mp hx⟩ hn
      rw [this] at h; exact Bool.noConfusion h
    · rintro ⟨v, hv, hs⟩
      cases hd : domAll u env d (fun v => !(eval u (v :: env) f && eval u (v :: env) b))
      · rfl
      · rw [domAll_iff] at hd
        have := hd v hv
        rw [(key v).mpr hs] at this
        exact Bool.noConfusion this

/-- A rule that `eval` accepts holds: the reflection step of a `holds` proof. -/
theorem holds_of_eval {u : Facts} {φ : Formula} (h : eval u [] φ = true) : Sat u [] φ :=
  (eval_iff u φ []).mp h

/-! ## Witnesses -/

/-- Is `v` in the domain? For entity domains through `find`, which `find_sound` makes exact. -/
def inDomB (u : Facts) (env : List Nat) : Dom → Nat → Bool
  | .any, v => match u.find v with | some _ => true | none => false
  | .kinds ks, v => match u.find v with | some e => memN e.kind ks | none => false
  | .term t, v => memN v (evalTerm u env t)

theorem inDomB_sound (u : Facts) (env : List Nat) (d : Dom) (v : Nat) :
    inDomB u env d v = true → InDom u env d v := by
  cases d with
  | any =>
    simp only [inDomB, InDom]
    split
    · rename_i e h; intro; exact ⟨e, Facts.find_sound u v e h⟩
    · simp
  | kinds ks =>
    simp only [inDomB, InDom]
    split
    · rename_i e h; intro hk
      have := Facts.find_sound u v e h
      exact ⟨e, this.1, this.2, (memN_iff _ _).mp hk⟩
    · simp
  | term t => simp [inDomB, InDom, memN_iff]

/-- Does `w` (values for the leading universal quantifiers, outermost first) falsify `φ`? -/
def refutes (u : Facts) : List Nat → Formula → List Nat → Bool
  | env, .all d f b, v :: w => inDomB u env d v && eval u (v :: env) f && refutes u (v :: env) b w
  | env, φ, [] => !eval u env φ
  | _, _, _ => false

theorem refutes_sound (u : Facts) : ∀ (env : List Nat) (φ : Formula) (w : List Nat),
    refutes u env φ w = true → ¬ Sat u env φ
  | env, .all d f b, v :: w, h => by
    simp only [refutes, Bool.and_eq_true] at h
    obtain ⟨⟨hd, hf⟩, hb⟩ := h
    intro hs
    exact refutes_sound u (v :: env) b w hb
      (hs v (inDomB_sound u env d v hd) ((eval_iff u f (v :: env)).mp hf))
  | env, .all d f b, [], h => by
    simp only [refutes, Bool.not_eq_true'] at h
    intro hs; rw [← eval_iff] at hs; simp_all
  | env, .tt, [], h | env, .ff, [], h | env, .eq _ _, [], h | env, .mem _ _, [], h
  | env, .nonempty _, [], h | env, .not _, [], h | env, .and _ _, [], h | env, .or _ _, [], h
  | env, .imp _ _, [], h | env, .ex _ _ _, [], h => by
    simp only [refutes, Bool.not_eq_true'] at h
    intro hs; rw [← eval_iff] at hs; simp_all
  | _, .tt, _ :: _, h | _, .ff, _ :: _, h | _, .eq _ _, _ :: _, h | _, .mem _ _, _ :: _, h
  | _, .nonempty _, _ :: _, h | _, .not _, _ :: _, h | _, .and _ _, _ :: _, h | _, .or _ _, _ :: _, h
  | _, .imp _ _, _ :: _, h | _, .ex _ _ _, _ :: _, h => by simp [refutes] at h

/-- A witness that `refutes` accepts proves the rule false: the step of a `violated` proof. -/
theorem violated_of_refutes {u : Facts} {φ : Formula} (w : List Nat) (h : refutes u [] φ w = true) :
    ¬ Sat u [] φ :=
  refutes_sound u [] φ w h

/-! ## Every witness, for the differential test -/

def domList (u : Facts) (env : List Nat) : Dom → List Nat
  | .any => u.toList.map (·.id)
  | .kinds ks => (u.toList.filter (fun e => memN e.kind ks)).map (·.id)
  | .term t => evalTerm u env t

/-- Every assignment of the leading universal quantifiers that passes the filters and falsifies
the body; `[[]]` for a false formula without one, `[]` for a true one. -/
def cex (u : Facts) : List Nat → Formula → List (List Nat)
  | env, .all d f b =>
    (domList u env d).flatMap fun v =>
      if eval u (v :: env) f then (cex u (v :: env) b).map (v :: ·) else []
  | env, φ => if eval u env φ then [] else [[]]

/-! ## The runner: `exegra-lean integrity` -/

open Exegra.Json in
private def num : Value → Except String Nat
  | .num x => pure x.toUInt64.toNat
  | _ => throw "integrity: expected a number"

open Exegra.Json in
private def nums : Value → Except String (List Nat)
  | .arr _ xs => xs.mapM num
  | _ => throw "integrity: expected an array of numbers"

private def field (fs : List (String × Value)) (k : String) : Value :=
  match fs.find? (·.1 == k) with | some (_, v) => v | none => .undef

private def obj : Value → Except String (List (String × Value))
  | .obj _ fs => pure fs
  | _ => throw "integrity: expected an object"

private partial def decodeTerm (v : Value) : Except String Term := do
  let fs ← obj v
  match field fs "t" with
  | .str "var" => return .var (← num (field fs "i"))
  | .str "lit" => return .lit (← nums (field fs "vs"))
  | .str "prop" => return .prop (← decodeTerm (field fs "of")) (← num (field fs "p"))
  | .str "kindOf" => return .kindOf (← decodeTerm (field fs "of"))
  | _ => throw "integrity: unknown term"

private def decodeDom (v : Value) : Except String Dom := do
  let fs ← obj v
  match field fs "t" with
  | .str "any" => return .any
  | .str "kinds" => return .kinds (← nums (field fs "ks"))
  | .str "term" => return .term (← decodeTerm (field fs "of"))
  | _ => throw "integrity: unknown domain"

private partial def decodeFormula (v : Value) : Except String Formula := do
  let fs ← obj v
  let f (k : String) := decodeFormula (field fs k)
  let t (k : String) := decodeTerm (field fs k)
  match field fs "t" with
  | .str "tt" => return .tt
  | .str "ff" => return .ff
  | .str "eq" => return .eq (← t "a") (← t "b")
  | .str "mem" => return .mem (← t "a") (← t "b")
  | .str "nonempty" => return .nonempty (← t "a")
  | .str "not" => return .not (← f "f")
  | .str "and" => return .and (← f "f") (← f "g")
  | .str "or" => return .or (← f "f") (← f "g")
  | .str "imp" => return .imp (← f "f") (← f "g")
  | .str "all" => return .all (← decodeDom (field fs "d")) (← f "f") (← f "b")
  | .str "ex" => return .ex (← decodeDom (field fs "d")) (← f "f") (← f "b")
  | _ => throw "integrity: unknown formula"

/-- Build a balanced search tree from entities sorted by id. -/
private partial def build (xs : Array Ent) (lo hi : Nat) : Facts :=
  if lo ≥ hi then .leaf else
  let mid := (lo + hi) / 2
  .node (build xs lo mid) xs[mid]! (build xs (mid + 1) hi)

private def decodeEnt (v : Value) : Except String Ent := do
  let fs ← obj v
  let props ← match field fs "props" with
    | .arr _ ps => ps.mapM fun p => do
        let pf ← obj p
        return ((← num (field pf "p")), (← nums (field pf "vs")))
    | _ => throw "integrity: \"props\" must be an array"
  return { id := (← num (field fs "id")), kind := (← num (field fs "kind")), props }

/-- Reads `{entities, rules: [{id, formula}]}` and writes per rule the verdict and every witness. -/
def runIntegrity (text : String) : Except String String := do
  let root ← obj (← Json.parse text)
  let ents ← match field root "entities" with
    | .arr _ xs => xs.mapM decodeEnt
    | _ => throw "integrity: \"entities\" must be an array"
  let sorted := (ents.toArray.qsort (fun a b => a.id < b.id))
  let u := build sorted 0 sorted.size
  let rules ← match field root "rules" with
    | .arr _ xs => xs.mapM fun r => do
        let fs ← obj r
        let id ← match field fs "id" with | .str s => pure s | _ => throw "integrity: a rule needs an id"
        return (id, ← decodeFormula (field fs "formula"))
    | _ => throw "integrity: \"rules\" must be an array"
  let out : List Value := rules.map fun (id, φ) =>
    let holds := eval u [] φ
    let ws := cex u [] φ
    .obj 0 [("id", .str id), ("holds", .bool holds),
      ("witnesses", .arr 0 (ws.map fun w => .arr 0 (w.map fun n => .num n.toFloat)))]
  return Json.write (.obj 0 [("searchTree", .bool (Facts.bst none none u)), ("results", .arr 0 out)])

/-- info: 'Exegra.Integrity.eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_iff

/-- info: 'Exegra.Integrity.refutes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refutes_sound

/-- info: 'Exegra.Integrity.Facts.find_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Facts.find_complete

end Exegra.Integrity
