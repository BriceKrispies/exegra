import Exegra.Json

/-
Integrity rules over a finite specification, decided in the kernel.

A rule of `src/core/integrity.js` is exported (`src/core/integrity-export.js`) as a `Formula` over
`Facts`: the entities the rule can reach, each with its kind and the values of only the properties
the rule reads. Every string (ids, kinds, property names, literals) is interned to a `Nat`, so the
kernel compares numbers (`Nat.beq`, `Nat.blt`, which it evaluates natively) and never strings.
Facts are a binary search tree keyed by entity id, so following a reference is a logarithmic walk.

* `Sat u I env φ` is the meaning of a formula, as a `Prop`, under an interpretation `I` of the
  derived relations (`integrityRelation`, atoms `.atom r ts`).
* `eval u T env φ` is a Bool checker by structural recursion over a Bool table `T`, so the kernel
  can evaluate it. `eval_iff` proves the two agree (`Sat u (toI T)`).
* Derived relations: `Least u prog` is the least-model meaning of a stratified program, defined
  impredicatively; `solve` is the checker that iterates the clauses to a fixpoint; `wf` decides
  stratification; `least_eq_table` proves that the solved table is exactly `Least`.
* A rule that holds is proved by reflection:
  `holds_of_eval prog_wf prog_solved (by decide +kernel) : Sat u (Least u prog) [] φ`, with no axiom
  beyond Lean's standard ones. A rule without relations has the empty program.
* `refutes u T env φ w` checks one witness: values for the leading universal quantifiers that
  are in range, pass the filters, and falsify the body. `refutes_sound` proves that such a witness
  refutes the rule, so a violation is proved from the concrete counterexample alone
  (`violated_of_refutes`, again under `Least`).
* `cex` lists every witness; `exegra-lean integrity` runs it for the differential test against the
  JavaScript evaluator, and reports the solved tables.
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
  /-- `atom r ts`: some choice of one value from each term of `ts`, in order, is a tuple of the
  derived relation `r`. -/
  | atom (r : Nat) (ts : List Term)

/-- An interpretation of the derived relations: the tuples each relation (by interned id) holds. -/
abbrev Interp := Nat → List Nat → Prop

def InDom (u : Facts) (env : List Nat) : Dom → Nat → Prop
  | .any, v => ∃ e, u.Mem e ∧ e.id = v
  | .kinds ks, v => ∃ e, u.Mem e ∧ e.id = v ∧ e.kind ∈ ks
  | .term t, v => v ∈ evalTerm u env t

/-- `Pick u env ts vs`: `vs` takes one value from each term of `ts`, in order. -/
def Pick (u : Facts) (env : List Nat) : List Term → List Nat → Prop
  | [], [] => True
  | t :: ts, v :: vs => v ∈ evalTerm u env t ∧ Pick u env ts vs
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- The meaning of a formula, under an interpretation `I` of the derived relations. -/
def Sat (u : Facts) (I : Interp) : List Nat → Formula → Prop
  | _, .tt => True
  | _, .ff => False
  | env, .eq a b => (∀ x ∈ evalTerm u env a, x ∈ evalTerm u env b) ∧ (∀ x ∈ evalTerm u env b, x ∈ evalTerm u env a)
  | env, .mem a b => evalTerm u env a ≠ [] ∧ ∀ x ∈ evalTerm u env a, x ∈ evalTerm u env b
  | env, .nonempty a => evalTerm u env a ≠ []
  | env, .not f => ¬ Sat u I env f
  | env, .and f g => Sat u I env f ∧ Sat u I env g
  | env, .or f g => Sat u I env f ∨ Sat u I env g
  | env, .imp f g => Sat u I env f → Sat u I env g
  | env, .all d f b => ∀ v, InDom u env d v → Sat u I (v :: env) f → Sat u I (v :: env) b
  | env, .ex d f b => ∃ v, InDom u env d v ∧ Sat u I (v :: env) f ∧ Sat u I (v :: env) b
  | env, .atom r ts => ∃ vs, Pick u env ts vs ∧ I r vs

/-- Every value of `d` satisfies `p`. -/
def domAll (u : Facts) (env : List Nat) (d : Dom) (p : Nat → Bool) : Bool :=
  match d with
  | .any => u.all (fun e => p e.id)
  | .kinds ks => u.all (fun e => !memN e.kind ks || p e.id)
  | .term t => allL p (evalTerm u env t)

/-- Some value of `d` satisfies `p`. -/
def domAny (u : Facts) (env : List Nat) (d : Dom) (p : Nat → Bool) : Bool :=
  !domAll u env d (fun v => !p v)

/-- Some choice of one value from each term satisfies `p`. -/
def pickAny (u : Facts) (env : List Nat) : (List Nat → Bool) → List Term → Bool
  | p, [] => p []
  | p, t :: ts => anyL (fun v => pickAny u env (fun vs => p (v :: vs)) ts) (evalTerm u env t)

theorem pickAny_iff (u : Facts) (env : List Nat) : ∀ (ts : List Term) (p : List Nat → Bool),
    pickAny u env p ts = true ↔ ∃ vs, Pick u env ts vs ∧ p vs = true
  | [], p => by
    simp only [pickAny]
    constructor
    · intro h; exact ⟨[], by simp [Pick], h⟩
    · rintro ⟨vs, hv, hp⟩
      cases vs with
      | nil => exact hp
      | cons _ _ => simp [Pick] at hv
  | t :: ts, p => by
    simp only [pickAny, anyL_iff, pickAny_iff u env ts]
    constructor
    · rintro ⟨v, hv, vs, hpk, hp⟩; exact ⟨v :: vs, ⟨hv, hpk⟩, hp⟩
    · rintro ⟨vs, hpk, hp⟩
      cases vs with
      | nil => simp [Pick] at hpk
      | cons v vs => exact ⟨v, hpk.1, vs, hpk.2, hp⟩

/-- The checker. `T` is a Bool table of the derived relations (`look` of a solved `Table`). -/
def eval (u : Facts) (T : Nat → List Nat → Bool) : List Nat → Formula → Bool
  | _, .tt => true
  | _, .ff => false
  | env, .eq a b =>
    allL (fun x => memN x (evalTerm u env b)) (evalTerm u env a) &&
    allL (fun x => memN x (evalTerm u env a)) (evalTerm u env b)
  | env, .mem a b => nonNil (evalTerm u env a) && allL (fun x => memN x (evalTerm u env b)) (evalTerm u env a)
  | env, .nonempty a => nonNil (evalTerm u env a)
  | env, .not f => !eval u T env f
  | env, .and f g => eval u T env f && eval u T env g
  | env, .or f g => eval u T env f || eval u T env g
  | env, .imp f g => !eval u T env f || eval u T env g
  | env, .all d f b => domAll u env d (fun v => !eval u T (v :: env) f || eval u T (v :: env) b)
  | env, .ex d f b => domAny u env d (fun v => eval u T (v :: env) f && eval u T (v :: env) b)
  | env, .atom r ts => pickAny u env (T r) ts

/-- The interpretation a Bool table stands for. -/
def toI (T : Nat → List Nat → Bool) : Interp := fun r vs => T r vs = true

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

theorem eval_iff (u : Facts) (T : Nat → List Nat → Bool) :
    ∀ (φ : Formula) (env : List Nat), eval u T env φ = true ↔ Sat u (toI T) env φ
  | .tt, _ => by simp [eval, Sat]
  | .ff, _ => by simp [eval, Sat]
  | .eq a b, env => by simp [eval, Sat, allL_iff, memN_iff]
  | .mem a b, env => by simp [eval, Sat, allL_iff, memN_iff, nonNil_iff]
  | .nonempty a, env => by simp [eval, Sat, nonNil_iff]
  | .not f, env => by simp [eval, Sat, ← eval_iff u T f env]
  | .and f g, env => by simp [eval, Sat, eval_iff u T f env, eval_iff u T g env]
  | .or f g, env => by simp [eval, Sat, eval_iff u T f env, eval_iff u T g env]
  | .imp f g, env => by
    simp only [eval, Sat, Bool.or_eq_true, Bool.not_eq_true', ← eval_iff u T f env, ← eval_iff u T g env]
    cases eval u T env f <;> simp
  | .all d f b, env => by
    simp only [eval, Sat, domAll_iff]
    apply forall_congr'; intro v; apply imp_congr_right; intro _
    rw [← eval_iff u T f (v :: env), ← eval_iff u T b (v :: env)]
    cases eval u T (v :: env) f <;> simp
  | .ex d f b, env => by
    have key : ∀ v, (eval u T (v :: env) f && eval u T (v :: env) b) = true ↔
        Sat u (toI T) (v :: env) f ∧ Sat u (toI T) (v :: env) b := by
      intro v; rw [Bool.and_eq_true, eval_iff u T f, eval_iff u T b]
    simp only [eval, Sat, domAny, Bool.not_eq_true']
    constructor
    · intro h
      apply Classical.byContradiction; intro hn
      have : domAll u env d (fun v => !(eval u T (v :: env) f && eval u T (v :: env) b)) = true := by
        rw [domAll_iff]; intro v hv
        cases hx : (eval u T (v :: env) f && eval u T (v :: env) b)
        · rfl
        · exact absurd ⟨v, hv, (key v).mp hx⟩ hn
      rw [this] at h; exact Bool.noConfusion h
    · rintro ⟨v, hv, hs⟩
      cases hd : domAll u env d (fun v => !(eval u T (v :: env) f && eval u T (v :: env) b))
      · rfl
      · rw [domAll_iff] at hd
        have := hd v hv
        rw [(key v).mpr hs] at this
        exact Bool.noConfusion this
  | .atom r ts, env => by simp only [eval, Sat, pickAny_iff, toI]

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
def refutes (u : Facts) (T : Nat → List Nat → Bool) : List Nat → Formula → List Nat → Bool
  | env, .all d f b, v :: w => inDomB u env d v && eval u T (v :: env) f && refutes u T (v :: env) b w
  | env, φ, [] => !eval u T env φ
  | _, _, _ => false

theorem refutes_sound (u : Facts) (T : Nat → List Nat → Bool) : ∀ (env : List Nat) (φ : Formula) (w : List Nat),
    refutes u T env φ w = true → ¬ Sat u (toI T) env φ
  | env, .all d f b, v :: w, h => by
    simp only [refutes, Bool.and_eq_true] at h
    obtain ⟨⟨hd, hf⟩, hb⟩ := h
    intro hs
    exact refutes_sound u T (v :: env) b w hb
      (hs v (inDomB_sound u env d v hd) ((eval_iff u T f (v :: env)).mp hf))
  | env, .all d f b, [], h => by
    simp only [refutes, Bool.not_eq_true'] at h
    intro hs; rw [← eval_iff] at hs; simp_all
  | env, .tt, [], h | env, .ff, [], h | env, .eq _ _, [], h | env, .mem _ _, [], h
  | env, .nonempty _, [], h | env, .not _, [], h | env, .and _ _, [], h | env, .or _ _, [], h
  | env, .imp _ _, [], h | env, .ex _ _ _, [], h | env, .atom _ _, [], h => by
    simp only [refutes, Bool.not_eq_true'] at h
    intro hs; rw [← eval_iff] at hs; simp_all
  | _, .tt, _ :: _, h | _, .ff, _ :: _, h | _, .eq _ _, _ :: _, h | _, .mem _ _, _ :: _, h
  | _, .nonempty _, _ :: _, h | _, .not _, _ :: _, h | _, .and _ _, _ :: _, h | _, .or _ _, _ :: _, h
  | _, .imp _ _, _ :: _, h | _, .ex _ _ _, _ :: _, h | _, .atom _ _, _ :: _, h => by simp [refutes] at h

/-! ## Every witness, for the differential test -/

def domList (u : Facts) (env : List Nat) : Dom → List Nat
  | .any => u.toList.map (·.id)
  | .kinds ks => (u.toList.filter (fun e => memN e.kind ks)).map (·.id)
  | .term t => evalTerm u env t

/-- Every assignment of the leading universal quantifiers that passes the filters and falsifies
the body; `[[]]` for a false formula without one, `[]` for a true one. -/
def cex (u : Facts) (T : Nat → List Nat → Bool) : List Nat → Formula → List (List Nat)
  | env, .all d f b =>
    (domList u env d).flatMap fun v =>
      if eval u T (v :: env) f then (cex u T (v :: env) b).map (v :: ·) else []
  | env, φ => if eval u T env φ then [] else [[]]

/-! ## Derived relations

A program is a list of strata, lowest first; a stratum is a list of relations. A relation has an
interned id, one domain per parameter (its candidate tuples are the product of the domains) and
clauses: formulas whose variables `0 .. n-1` are the parameters (`env` is the tuple itself).

* `Least u prog` is the meaning: stratum by stratum, a tuple is in a relation of the stratum iff it
  is in that relation in EVERY interpretation that agrees with the strata below and is closed
  under the stratum's clauses. It is defined impredicatively and does not mention the checker.
* `solve u prog []` is the checker: per stratum, it iterates the clauses from the empty table over
  the candidate tuples until nothing changes, with fuel; running out of fuel is `none`, a failure.
* `wf prog` is the stratification check, decided by the kernel: within a stratum every atom of a
  relation of that stratum occurs positively (`posF`), ids are distinct, and every atom names a
  relation of the stratum or below with its arity.
* `least_eq_table`: if `wf prog` and `solve u prog [] = some T`, then `Least u prog` is exactly
  the tuples of `T`. The two halves are `stratum_closed` (the table is closed under the clauses)
  and `stratum_le_closed` (the table is contained in every closed interpretation), the latter by
  `sat_mono`: a formula whose stratum atoms are all positive is monotone in them.
-/

theorem Facts.mem_toList : ∀ (t : Facts) (e : Ent), e ∈ t.toList ↔ t.Mem e
  | .leaf, e => by simp [Facts.toList, Facts.Mem]
  | .node l c r, e => by
    simp only [Facts.toList, Facts.Mem, List.mem_append, List.mem_cons, Facts.mem_toList l e,
      Facts.mem_toList r e]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem domList_iff (u : Facts) (env : List Nat) (d : Dom) (v : Nat) :
    v ∈ domList u env d ↔ InDom u env d v := by
  cases d with
  | any => simp only [domList, InDom, List.mem_map, Facts.mem_toList]
  | kinds ks =>
    simp only [domList, InDom, List.mem_map, List.mem_filter, Facts.mem_toList, memN_iff]
    constructor
    · rintro ⟨e, ⟨he, hk⟩, rfl⟩; exact ⟨e, he, rfl, hk⟩
    · rintro ⟨e, he, rfl, hk⟩; exact ⟨e, ⟨he, hk⟩, rfl⟩
  | term t => exact Iff.rfl

/-- `vs` is a candidate tuple: one value from each parameter domain. -/
def InDoms (u : Facts) : List Dom → List Nat → Prop
  | [], [] => True
  | d :: ds, v :: vs => InDom u [] d v ∧ InDoms u ds vs
  | [], _ :: _ => False
  | _ :: _, [] => False

def prodL : List (List Nat) → List (List Nat)
  | [] => [[]]
  | d :: ds => d.flatMap fun v => (prodL ds).map (v :: ·)

/-- The candidate tuples of a relation, in lexicographic order of the domains. -/
def cands (u : Facts) (ds : List Dom) : List (List Nat) := prodL (ds.map (domList u []))

theorem mem_cands (u : Facts) : ∀ (ds : List Dom) (vs : List Nat), vs ∈ cands u ds ↔ InDoms u ds vs
  | [], vs => by cases vs <;> simp [cands, prodL, InDoms]
  | d :: ds, [] => by simp [cands, prodL, InDoms]
  | d :: ds, v :: vs => by
    have ih := mem_cands u ds vs
    simp only [cands] at ih
    simp only [cands, List.map, prodL, List.mem_flatMap, List.mem_map, InDoms, ← ih, ← domList_iff]
    constructor
    · rintro ⟨w, hw, ws, hws, h⟩
      injection h with h1 h2
      subst h1; subst h2; exact ⟨hw, hws⟩
    · rintro ⟨hv, hvs⟩; exact ⟨v, hv, vs, hvs, rfl⟩

/-- Tables: per relation id, its tuples. -/
abbrev Table := List (Nat × List (List Nat))

def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && eqL xs ys
  | [], _ :: _ => false
  | _ :: _, [] => false

theorem eqL_iff : ∀ a b : List Nat, eqL a b = true ↔ a = b
  | [], [] => by simp [eqL]
  | x :: xs, y :: ys => by
    simp only [eqL, Bool.and_eq_true, eqL_iff xs ys, List.cons.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨Nat.eq_of_beq_eq_true h, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨Nat.beq_refl x, rfl⟩
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]

def memT (vs : List Nat) : List (List Nat) → Bool
  | [] => false
  | w :: ws => eqL vs w || memT vs ws

theorem memT_iff (vs : List Nat) : ∀ l, memT vs l = true ↔ vs ∈ l
  | [] => by simp [memT]
  | w :: ws => by simp only [memT, Bool.or_eq_true, eqL_iff, memT_iff vs ws, List.mem_cons]

/-- The tuples of relation `r`: the first entry for `r`, none without one. -/
def lookE : Table → Nat → List (List Nat)
  | [], _ => []
  | (q, ts) :: rest, r => if Nat.beq r q then ts else lookE rest r

def look (T : Table) (r : Nat) (vs : List Nat) : Bool := memT vs (lookE T r)

def hasKey : Table → Nat → Bool
  | [], _ => false
  | (q, _) :: rest, r => Nat.beq r q || hasKey rest r

theorem lookE_append (B : Table) (r : Nat) : ∀ A : Table,
    lookE (A ++ B) r = if hasKey A r then lookE A r else lookE B r
  | [] => by simp [hasKey]
  | (q, ts) :: rest => by
    simp only [List.cons_append, lookE, hasKey]
    by_cases h : Nat.beq r q = true
    · simp [h]
    · simp [h, lookE_append B r rest]

structure Rel where
  id : Nat
  doms : List Dom
  clauses : List Formula

/-- Strata, lowest first. -/
abbrev Program := List (List Rel)

def ids (s : List Rel) : List Nat := s.map (·.id)

/-- A table with one entry per relation of `s`. -/
def full (s : List Rel) (g : Rel → List (List Nat)) : Table := s.map fun ρ => (ρ.id, g ρ)

theorem hasKey_full (r : Nat) (g : Rel → List (List Nat)) : ∀ s : List Rel,
    hasKey (full s g) r = memN r (ids s)
  | [] => rfl
  | ρ :: s => by
    show (Nat.beq r ρ.id || hasKey (full s g) r) = (Nat.beq r ρ.id || memN r (ids s))
    rw [hasKey_full r g s]

theorem lookE_full_nil (r : Nat) : ∀ s : List Rel, lookE (full s fun _ => []) r = []
  | [] => rfl
  | ρ :: s => by
    show (if Nat.beq r ρ.id then [] else lookE (full s fun _ => []) r) = []
    rw [lookE_full_nil r s]; simp

def nodupN : List Nat → Bool
  | [] => true
  | x :: xs => !memN x xs && nodupN xs

theorem mem_ids_of_mem {ρ : Rel} {s : List Rel} (h : ρ ∈ s) : memN ρ.id (ids s) = true :=
  (memN_iff _ _).mpr (List.mem_map.mpr ⟨ρ, h, rfl⟩)

theorem mem_ids {r : Nat} {s : List Rel} (h : memN r (ids s) = true) : ∃ ρ ∈ s, ρ.id = r := by
  rw [memN_iff] at h
  simpa [ids] using h

theorem lookE_full (g : Rel → List (List Nat)) : ∀ (s : List Rel), nodupN (ids s) = true →
    ∀ ρ ∈ s, lookE (full s g) ρ.id = g ρ
  | [], _, ρ, h => by simp at h
  | σ :: s, hnd, ρ, hm => by
    have hnd' : (!memN σ.id (ids s) && nodupN (ids s)) = true := hnd
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hnd'
    show (if Nat.beq ρ.id σ.id then g σ else lookE (full s g) ρ.id) = g ρ
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [Nat.beq_refl]
    · have hne : Nat.beq ρ.id σ.id = false := by
        cases h : Nat.beq ρ.id σ.id
        · rfl
        · have heq := Nat.eq_of_beq_eq_true h
          have := mem_ids_of_mem hm
          rw [heq, hnd'.1] at this
          exact absurd this (by decide)
      rw [hne]
      exact lookE_full g s hnd'.2 ρ hm

theorem look_full_in {s : List Rel} {g : Rel → List (List Nat)} {Tl : Table} {r : Nat} {vs : List Nat}
    (h : memN r (ids s) = true) : look (full s g ++ Tl) r vs = look (full s g) r vs := by
  simp only [look, lookE_append, hasKey_full, h, ↓reduceIte]

theorem look_full_out {s : List Rel} {g : Rel → List (List Nat)} {Tl : Table} {r : Nat} {vs : List Nat}
    (h : memN r (ids s) = false) : look (full s g ++ Tl) r vs = look Tl r vs := by
  simp [look, lookE_append, hasKey_full, h]

/-! ### Positivity and monotonicity -/

/-- Every atom of a relation in `S` occurs with polarity `p` (`true`: positively). `!` flips, the
left side of `=>` flips, a `forall` filter flips, an `exists` filter does not. Quantifier domains
are terms, which contain no atoms. -/
def posF (S : List Nat) : Bool → Formula → Bool
  | _, .tt | _, .ff | _, .eq _ _ | _, .mem _ _ | _, .nonempty _ => true
  | p, .not f => posF S (!p) f
  | p, .and f g => posF S p f && posF S p g
  | p, .or f g => posF S p f && posF S p g
  | p, .imp f g => posF S (!p) f && posF S p g
  | p, .all _ f b => posF S (!p) f && posF S p b
  | p, .ex _ f b => posF S p f && posF S p b
  | p, .atom r _ => p || !memN r S

/-- Monotonicity: if `I ≤ J` on the relations of `S` and they agree elsewhere, a formula in which
the atoms of `S` occur with polarity `p` goes up from `I` to `J` (`p = true`) or down (`false`). -/
theorem sat_mono (u : Facts) (S : List Nat) (I J : Interp)
    (hin : ∀ r, memN r S = true → ∀ vs, I r vs → J r vs)
    (hout : ∀ r, memN r S = false → ∀ vs, (I r vs ↔ J r vs)) :
    ∀ (φ : Formula) (p : Bool) (env : List Nat), posF S p φ = true →
      (p = true → Sat u I env φ → Sat u J env φ) ∧ (p = false → Sat u J env φ → Sat u I env φ)
  | .tt, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .ff, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .eq _ _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .mem _ _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .nonempty _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .not f, p, env, h => by
    have ih := sat_mono u S I J hin hout f (!p) env h
    simp only [Sat]
    constructor
    · intro hp hs hj; exact hs (ih.2 (by simp [hp]) hj)
    · intro hp hs hi; exact hs (ih.1 (by simp [hp]) hi)
  | .and f g, p, env, h => by
    simp only [posF, Bool.and_eq_true] at h
    have ihf := sat_mono u S I J hin hout f p env h.1
    have ihg := sat_mono u S I J hin hout g p env h.2
    simp only [Sat]
    exact ⟨fun hp hs => ⟨ihf.1 hp hs.1, ihg.1 hp hs.2⟩, fun hp hs => ⟨ihf.2 hp hs.1, ihg.2 hp hs.2⟩⟩
  | .or f g, p, env, h => by
    simp only [posF, Bool.and_eq_true] at h
    have ihf := sat_mono u S I J hin hout f p env h.1
    have ihg := sat_mono u S I J hin hout g p env h.2
    simp only [Sat]
    exact ⟨fun hp hs => hs.elim (fun a => Or.inl (ihf.1 hp a)) (fun b => Or.inr (ihg.1 hp b)),
      fun hp hs => hs.elim (fun a => Or.inl (ihf.2 hp a)) (fun b => Or.inr (ihg.2 hp b))⟩
  | .imp f g, p, env, h => by
    simp only [posF, Bool.and_eq_true] at h
    have ihf := sat_mono u S I J hin hout f (!p) env h.1
    have ihg := sat_mono u S I J hin hout g p env h.2
    simp only [Sat]
    constructor
    · intro hp hs hj; exact ihg.1 hp (hs (ihf.2 (by simp [hp]) hj))
    · intro hp hs hi; exact ihg.2 hp (hs (ihf.1 (by simp [hp]) hi))
  | .all d f b, p, env, h => by
    simp only [posF, Bool.and_eq_true] at h
    simp only [Sat]
    constructor
    · intro hp hs v hv hj
      have ihf := sat_mono u S I J hin hout f (!p) (v :: env) h.1
      have ihb := sat_mono u S I J hin hout b p (v :: env) h.2
      exact ihb.1 hp (hs v hv (ihf.2 (by simp [hp]) hj))
    · intro hp hs v hv hi
      have ihf := sat_mono u S I J hin hout f (!p) (v :: env) h.1
      have ihb := sat_mono u S I J hin hout b p (v :: env) h.2
      exact ihb.2 hp (hs v hv (ihf.1 (by simp [hp]) hi))
  | .ex d f b, p, env, h => by
    simp only [posF, Bool.and_eq_true] at h
    simp only [Sat]
    constructor
    · rintro hp ⟨v, hv, hf, hb⟩
      exact ⟨v, hv, (sat_mono u S I J hin hout f p (v :: env) h.1).1 hp hf,
        (sat_mono u S I J hin hout b p (v :: env) h.2).1 hp hb⟩
    · rintro hp ⟨v, hv, hf, hb⟩
      exact ⟨v, hv, (sat_mono u S I J hin hout f p (v :: env) h.1).2 hp hf,
        (sat_mono u S I J hin hout b p (v :: env) h.2).2 hp hb⟩
  | .atom r ts, p, env, h => by
    simp only [posF, Bool.or_eq_true, Bool.not_eq_true'] at h
    simp only [Sat]
    constructor
    · rintro rfl ⟨vs, hv, hi⟩
      refine ⟨vs, hv, ?_⟩
      cases hr : memN r S
      · exact (hout r hr vs).mp hi
      · exact hin r hr vs hi
    · rintro rfl ⟨vs, hv, hj⟩
      have hr : memN r S = false := by simpa using h
      exact ⟨vs, hv, (hout r hr vs).mpr hj⟩

/-! ### The meaning: least models, stratum by stratum -/

/-- `I` agrees with `L` outside the relations `S`. -/
def Agree (S : List Nat) (I L : Interp) : Prop := ∀ r, memN r S = false → ∀ vs, (I r vs ↔ L r vs)

/-- `I` is closed under the clauses of the stratum `s`: every candidate tuple that satisfies a
clause of its relation is in the relation. -/
def ClosedS (u : Facts) (I : Interp) (s : List Rel) : Prop :=
  ∀ ρ ∈ s, ∀ vs, InDoms u ρ.doms vs → ∀ c ∈ ρ.clauses, Sat u I vs c → I ρ.id vs

/-- The least interpretation of stratum `s` over the lower strata `L`: a tuple is in a relation of
`s` iff it is in it in every interpretation that agrees with `L` outside `s` and is closed under
the clauses of `s`. Outside `s` it is `L`. -/
def LeastS (u : Facts) (L : Interp) (s : List Rel) : Interp := fun r vs =>
  if memN r (ids s) = true then ∀ I : Interp, Agree (ids s) I L → ClosedS u I s → I r vs else L r vs

def Meaning (u : Facts) : Program → Interp → Interp
  | [], L => L
  | s :: rest, L => Meaning u rest (LeastS u L s)

/-- The meaning of a program: its strata's least models, lowest first, from no tuples at all. -/
def Least (u : Facts) (prog : Program) : Interp := Meaning u prog (fun _ _ => False)

/-! ### The checker -/

/-- One relation's tuples after a step from `T`: the candidates satisfying a clause under `T` (the
stratum) over `Tl` (the strata below). The clauses are positive in the stratum, so the iterates
grow; the old row is not consulted, which spares the kernel a scan of it per candidate. -/
def stepRow (u : Facts) (Tl T : Table) (ρ : Rel) : List (List Nat) :=
  (cands u ρ.doms).filter fun vs => ρ.clauses.any fun c => eval u (look (T ++ Tl)) vs c

def stepS (u : Facts) (Tl : Table) (s : List Rel) (T : Table) : Table := full s (stepRow u Tl T)

def sumN : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumN xs

/-- Enough steps: every step before the fixpoint adds a candidate tuple. -/
def fuelS (u : Facts) (s : List Rel) : Nat := sumN (s.map fun ρ => (cands u ρ.doms).length) + 2

/-- Iterate to the fixpoint; `none` when the fuel runs out (a failure, never a wrong table). -/
def solveS (u : Facts) (Tl : Table) (s : List Rel) : Nat → Table → Option Table
  | 0, _ => none
  | n + 1, T => if stepS u Tl s T = T then some T else solveS u Tl s n (stepS u Tl s T)

/-- Solve the strata lowest first; the result lists the higher strata first. -/
def solve (u : Facts) : Program → Table → Option Table
  | [], Tl => some Tl
  | s :: rest, Tl =>
    match solveS u Tl s (fuelS u s) (full s fun _ => []) with
    | some Ts => solve u rest (Ts ++ Tl)
    | none => none

/-! ### Stratification, decided by the kernel -/

/-- Every atom names a relation of `A` (id, arity) with its arity. -/
def arityOK (A : List (Nat × Nat)) : Formula → Bool
  | .tt | .ff | .eq _ _ | .mem _ _ | .nonempty _ => true
  | .not f => arityOK A f
  | .and f g | .or f g | .imp f g => arityOK A f && arityOK A g
  | .all _ f b | .ex _ f b => arityOK A f && arityOK A b
  | .atom r ts => A.any fun p => Nat.beq p.1 r && Nat.beq p.2 ts.length

/-- Per stratum: distinct ids, not defined below; every clause positive in the stratum's own
relations and naming only relations of the stratum or below, with their arity. -/
def wfGo : List (Nat × Nat) → Program → Bool
  | _, [] => true
  | A, s :: rest =>
    let A' := s.map (fun ρ => (ρ.id, ρ.doms.length)) ++ A
    nodupN (ids s) &&
    s.all (fun ρ => !A.any (fun p => Nat.beq p.1 ρ.id)) &&
    s.all (fun ρ => ρ.clauses.all fun c => posF (ids s) true c && arityOK A' c) &&
    wfGo A' rest

def wf (prog : Program) : Bool := wfGo [] prog

theorem wfGo_cons {A : List (Nat × Nat)} {s : List Rel} {rest : Program} (h : wfGo A (s :: rest) = true) :
    nodupN (ids s) = true ∧ (∀ ρ ∈ s, ∀ c ∈ ρ.clauses, posF (ids s) true c = true) ∧
    wfGo (s.map (fun ρ => (ρ.id, ρ.doms.length)) ++ A) rest = true := by
  simp only [wfGo, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, _⟩, h3⟩, h4⟩ := h
  exact ⟨h1, fun ρ hρ c hc => (h3 ρ hρ c hc).1, h4⟩

/-! ### The checker computes the least model -/

/-- What every iterate of a stratum satisfies: one entry per relation, and each of its tuples is in
every interpretation that agrees with `L` outside the stratum and is closed under its clauses. -/
def Below (u : Facts) (s : List Rel) (L : Interp) (T : Table) : Prop :=
  (∃ g, T = full s g) ∧
  ∀ I, Agree (ids s) I L → ClosedS u I s → ∀ r, memN r (ids s) = true → ∀ vs, look T r vs = true → I r vs

theorem below_empty (u : Facts) (s : List Rel) (L : Interp) : Below u s L (full s fun _ => []) := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro I _ _ r _ vs h
  simp [look, lookE_full_nil, memT] at h

theorem below_step (u : Facts) (Tl : Table) (s : List Rel) (L : Interp)
    (hL : ∀ r vs, L r vs ↔ look Tl r vs = true) (hnd : nodupN (ids s) = true)
    (hpos : ∀ ρ ∈ s, ∀ c ∈ ρ.clauses, posF (ids s) true c = true)
    {T : Table} (hT : Below u s L T) : Below u s L (stepS u Tl s T) := by
  obtain ⟨⟨g, rfl⟩, hle⟩ := hT
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro I hag hcl r hr vs h
  obtain ⟨ρ, hρ, rfl⟩ := mem_ids hr
  have h' : memT vs (lookE (full s (stepRow u Tl (full s g))) ρ.id) = true := h
  rw [lookE_full _ s hnd ρ hρ, memT_iff, stepRow, List.mem_filter, List.any_eq_true] at h'
  obtain ⟨hc, c, hcm, he⟩ := h'
  have hsat := (eval_iff u _ c vs).mp he
  have hmono := sat_mono u (ids s) (toI (look (full s g ++ Tl))) I
    (fun r' hr' ws hw => by
      have hw' : look (full s g ++ Tl) r' ws = true := hw
      rw [look_full_in hr'] at hw'
      exact hle I hag hcl r' hr' ws hw')
    (fun r' hr' ws => by
      show look (full s g ++ Tl) r' ws = true ↔ I r' ws
      rw [look_full_out hr', ← hL r' ws]
      exact (hag r' hr' ws).symm)
    c true vs (hpos ρ hρ c hcm)
  exact hcl ρ hρ vs ((mem_cands u ρ.doms vs).mp hc) c hcm (hmono.1 rfl hsat)

theorem solveS_spec (u : Facts) (Tl : Table) (s : List Rel) (L : Interp)
    (hL : ∀ r vs, L r vs ↔ look Tl r vs = true) (hnd : nodupN (ids s) = true)
    (hpos : ∀ ρ ∈ s, ∀ c ∈ ρ.clauses, posF (ids s) true c = true) :
    ∀ (n : Nat) (T Ts : Table), Below u s L T → solveS u Tl s n T = some Ts →
      Below u s L Ts ∧ stepS u Tl s Ts = Ts
  | 0, _, _, _, h => by simp [solveS] at h
  | n + 1, T, Ts, hT, h => by
    simp only [solveS] at h
    split at h
    · rename_i heq
      injection h with h
      subst h
      exact ⟨hT, heq⟩
    · exact solveS_spec u Tl s L hL hnd hpos n _ Ts (below_step u Tl s L hL hnd hpos hT) h

/-- (a) A fixpoint of the step is closed under the stratum's clauses. -/
theorem fix_closed (u : Facts) (Tl : Table) (s : List Rel) (hnd : nodupN (ids s) = true)
    {Ts : Table} (hfull : ∃ g, Ts = full s g) (hfix : stepS u Tl s Ts = Ts) :
    ClosedS u (toI (look (Ts ++ Tl))) s := by
  obtain ⟨g, rfl⟩ := hfull
  intro ρ hρ vs hvs c hc hsat
  have hr := mem_ids_of_mem hρ
  show look (full s g ++ Tl) ρ.id vs = true
  rw [look_full_in hr, ← hfix]
  show memT vs (lookE (full s (stepRow u Tl (full s g))) ρ.id) = true
  rw [lookE_full _ s hnd ρ hρ, memT_iff, stepRow, List.mem_filter]
  refine ⟨(mem_cands u ρ.doms vs).mpr hvs, ?_⟩
  rw [List.any_eq_true]
  exact ⟨c, hc, (eval_iff u _ c vs).mpr hsat⟩

/-- (a) The solved table of a stratum is closed under its clauses. -/
theorem stratum_closed (u : Facts) (Tl : Table) (s : List Rel) (L : Interp)
    (hL : ∀ r vs, L r vs ↔ look Tl r vs = true) (hnd : nodupN (ids s) = true)
    (hpos : ∀ ρ ∈ s, ∀ c ∈ ρ.clauses, posF (ids s) true c = true) {Ts : Table}
    (hs : solveS u Tl s (fuelS u s) (full s fun _ => []) = some Ts) :
    ClosedS u (toI (look (Ts ++ Tl))) s :=
  have h := solveS_spec u Tl s L hL hnd hpos _ _ Ts (below_empty u s L) hs
  fix_closed u Tl s hnd h.1.1 h.2

/-- (b) The solved table of a stratum is contained in every interpretation that agrees with the
strata below and is closed under the stratum's clauses. -/
theorem stratum_le_closed (u : Facts) (Tl : Table) (s : List Rel) (L : Interp)
    (hL : ∀ r vs, L r vs ↔ look Tl r vs = true) (hnd : nodupN (ids s) = true)
    (hpos : ∀ ρ ∈ s, ∀ c ∈ ρ.clauses, posF (ids s) true c = true) {Ts : Table}
    (hs : solveS u Tl s (fuelS u s) (full s fun _ => []) = some Ts) :
    ∀ I, Agree (ids s) I L → ClosedS u I s → ∀ r, memN r (ids s) = true → ∀ vs,
      look Ts r vs = true → I r vs :=
  (solveS_spec u Tl s L hL hnd hpos _ _ Ts (below_empty u s L) hs).1.2

/-- A stratum's least model is its solved table (over the strata below). -/
theorem stratum_least (u : Facts) (Tl : Table) (s : List Rel) (L : Interp)
    (hL : ∀ r vs, L r vs ↔ look Tl r vs = true) (hnd : nodupN (ids s) = true)
    (hpos : ∀ ρ ∈ s, ∀ c ∈ ρ.clauses, posF (ids s) true c = true) {Ts : Table}
    (hs : solveS u Tl s (fuelS u s) (full s fun _ => []) = some Ts) :
    ∀ r vs, LeastS u L s r vs ↔ look (Ts ++ Tl) r vs = true := by
  have hspec := solveS_spec u Tl s L hL hnd hpos _ _ Ts (below_empty u s L) hs
  obtain ⟨g, hg⟩ := hspec.1.1
  intro r vs
  unfold LeastS
  cases hr : memN r (ids s)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hg, look_full_out hr]
    exact hL r vs
  · simp only [↓reduceIte]
    constructor
    · intro h
      refine h _ ?_ (stratum_closed u Tl s L hL hnd hpos hs)
      intro q hq ws
      show look (Ts ++ Tl) q ws = true ↔ L q ws
      rw [hg, look_full_out hq]
      exact (hL q ws).symm
    · intro h I hag hcl
      rw [hg, look_full_in hr, ← hg] at h
      exact stratum_le_closed u Tl s L hL hnd hpos hs I hag hcl r hr vs h

theorem solve_correct (u : Facts) : ∀ (prog : Program) (A : List (Nat × Nat)) (L : Interp) (Tl T : Table),
    wfGo A prog = true → (∀ r vs, L r vs ↔ look Tl r vs = true) → solve u prog Tl = some T →
    ∀ r vs, Meaning u prog L r vs ↔ look T r vs = true
  | [], _, L, Tl, T, _, hL, hs => by
    simp only [solve, Option.some.injEq] at hs
    subst hs
    exact hL
  | s :: rest, A, L, Tl, T, hw, hL, hs => by
    obtain ⟨hnd, hpos, hw'⟩ := wfGo_cons hw
    unfold solve at hs
    revert hs
    cases hTs : solveS u Tl s (fuelS u s) (full s fun _ => []) with
    | none => intro hs; simp at hs
    | some Ts =>
      intro hs
      exact solve_correct u rest _ (LeastS u L s) (Ts ++ Tl) T hw'
        (stratum_least u Tl s L hL hnd hpos hTs) hs

/-- The least-model result: for a stratified program that the checker solves, the meaning
`Least` (defined without the checker) holds exactly the tuples of the checker's table. -/
theorem least_eq_table {u : Facts} {prog : Program} {T : Table} (hw : wf prog = true)
    (hs : solve u prog [] = some T) : ∀ r vs, Least u prog r vs ↔ look T r vs = true :=
  solve_correct u prog [] _ [] T hw (fun r vs => by simp [look, lookE, memT]) hs

theorem least_eq {u : Facts} {prog : Program} {T : Table} (hw : wf prog = true)
    (hs : solve u prog [] = some T) : Least u prog = toI (look T) :=
  funext fun r => funext fun vs => propext (least_eq_table hw hs r vs)

/-- A rule that `eval` accepts over the solved table holds under the least-model meaning: the
reflection step of a `holds` proof. -/
theorem holds_of_eval {u : Facts} {prog : Program} {T : Table} {φ : Formula} (hw : wf prog = true)
    (hs : solve u prog [] = some T) (h : eval u (look T) [] φ = true) : Sat u (Least u prog) [] φ := by
  rw [least_eq hw hs]
  exact (eval_iff u (look T) φ []).mp h

/-- A witness that `refutes` accepts over the solved table proves the rule false under the
least-model meaning: the step of a `violated` proof. -/
theorem violated_of_refutes {u : Facts} {prog : Program} {T : Table} {φ : Formula} (w : List Nat)
    (hw : wf prog = true) (hs : solve u prog [] = some T) (h : refutes u (look T) [] φ w = true) :
    ¬ Sat u (Least u prog) [] φ := by
  rw [least_eq hw hs]
  exact refutes_sound u (look T) [] φ w h

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

private def arr (what : String) : Value → Except String (List Value)
  | .arr _ xs => pure xs
  | _ => throw s!"integrity: \"{what}\" must be an array"

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
  | .str "atom" => return .atom (← num (field fs "r")) (← (← arr "ts" (field fs "ts")).mapM decodeTerm)
  | _ => throw "integrity: unknown formula"

private def decodeRel (v : Value) : Except String Rel := do
  let fs ← obj v
  let doms ← (← arr "doms" (field fs "doms")).mapM decodeDom
  let clauses ← (← arr "clauses" (field fs "clauses")).mapM decodeFormula
  return { id := (← num (field fs "id")), doms, clauses }

/-- The program: `"program"`, strata lowest first; absent for a rule that uses no relation. -/
private def decodeProgram (v : Value) : Except String Program :=
  match v with
  | .undef => pure []
  | _ => do (← arr "program" v).mapM fun s => do (← arr "stratum" s).mapM decodeRel

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

private def tuplesJson (ts : List (List Nat)) : Value :=
  .arr 0 (ts.map fun w => .arr 0 (w.map fun n => .num n.toFloat))

/-- Reads `{entities, program?, rules: [{id, formula}]}` and writes whether the program is
stratified (`wf`), whether the checker solved it, the solved tables (higher strata first, as
`solve` lists them), and per rule the verdict and every witness over those tables. -/
def runIntegrity (text : String) : Except String String := do
  let root ← obj (← Json.parse text)
  let ents ← match field root "entities" with
    | .arr _ xs => xs.mapM decodeEnt
    | _ => throw "integrity: \"entities\" must be an array"
  let sorted := (ents.toArray.qsort (fun a b => a.id < b.id))
  let u := build sorted 0 sorted.size
  let prog ← decodeProgram (field root "program")
  let rules ← match field root "rules" with
    | .arr _ xs => xs.mapM fun r => do
        let fs ← obj r
        let id ← match field fs "id" with | .str s => pure s | _ => throw "integrity: a rule needs an id"
        return (id, ← decodeFormula (field fs "formula"))
    | _ => throw "integrity: \"rules\" must be an array"
  let solved := solve u prog []
  let T := solved.getD []
  let out : List Value := rules.map fun (id, φ) =>
    let holds := eval u (look T) [] φ
    let ws := cex u (look T) [] φ
    .obj 0 [("id", .str id), ("holds", .bool holds),
      ("witnesses", .arr 0 (ws.map fun w => .arr 0 (w.map fun n => .num n.toFloat)))]
  let tables : List Value := T.map fun (r, ts) => .obj 0 [("id", .num r.toFloat), ("tuples", tuplesJson ts)]
  return Json.write (.obj 0 [("searchTree", .bool (Facts.bst none none u)), ("wf", .bool (wf prog)),
    ("solved", .bool solved.isSome), ("tables", .arr 0 tables), ("results", .arr 0 out)])

/-- info: 'Exegra.Integrity.eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_iff

/-- info: 'Exegra.Integrity.refutes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refutes_sound

/-- info: 'Exegra.Integrity.Facts.find_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Facts.find_complete

/-- info: 'Exegra.Integrity.sat_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sat_mono

/-- info: 'Exegra.Integrity.stratum_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stratum_closed

/-- info: 'Exegra.Integrity.stratum_le_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stratum_le_closed

/-- info: 'Exegra.Integrity.stratum_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stratum_least

/-- info: 'Exegra.Integrity.solve_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solve_correct

/-- info: 'Exegra.Integrity.least_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms least_eq_table

/-- info: 'Exegra.Integrity.holds_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms holds_of_eval

/-- info: 'Exegra.Integrity.violated_of_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms violated_of_refutes
end Exegra.Integrity
