import Std.Data.HashMap
import Std.Data.HashSet
import Exegra.Json
import Exegra.Value

/-!
Structural multiscale semantics: the formal grounding of the abstraction engine
(`src/core/abstraction.js`; WG-5699, task WG-5740).

A hierarchy (a forest, given by a parent function and a fuel bound) and a cut of it (a set of blocks)
send every element to its block `alpha`: its ancestor-or-self on the cut, or itself when the cut opens
it. A fact base (relationships between elements) is then lifted to the cut: for blocks `X ≠ Y` and a
kind `k` the interaction `(X, Y, k)` has the witness list of the facts from a member of `X` to a member
of `Y` of (coarsened) kind `k`; the fibre of `X` is the facts inside `X`; the boundary of `X` is the
facts with exactly one end in `X`.

Proof map (every theorem below is guarded by `#print axioms` at the end of the file):

* P1  `p1_alpha_unique`, `p1_alpha_total` (`alpha_spec`, `alpha_of_no_block` complete the picture)
* P2  `p2_cut_compose`
* P3  `p3_lift_functorial`, `p3_summary_hom` (`summary_append`), `p3_coarsen_compose`,
      `p3_coarsen_union`
* P4  `p4_absence_transfer`, `p4_absence_class`
* P5  `p5_boundary_determines_interface`, `p5_boundary_compose`
* P6  `p6_reach_up`, `p6_acyclic_down`, `p6_spurious_path`
* P7  `p7_recover`, `p7_unique_fibre`, `p7_unique_key`, `p7_exclusive`, `p7_sub`
* P13 `p13_incremental`, `p13_incremental_list`, `p13_incremental_fibre`,
      `p13_incremental_fibre_list`

Everything generic is over an element type `α` with decidable equality. The executable part
(`deriveValue`) instantiates it at `String` with the SAME definitions (`alpha`, `witnessesBy`,
`fibreBy`, `outBy`, `innBy`; the `H C`-indexed `witnesses`, `fibre`, `out`, `inn` are those with
`alpha H C` supplied), so a differential check against the JavaScript tests the proved definitions.
The executable part supplies a table-backed copy of `alpha` (computed once per endpoint) to the
`By` definitions; that table is `alpha` evaluated on every fact endpoint.

What is assumed of a hierarchy: `Hier.Stable` (the ancestor chain of every element is complete within
the fuel `n`; true of any forest with at most `n` elements). P1 needs no hypothesis on the hierarchy
at all; transitivity of the ancestor relation (P2, P3, P5) needs `Stable`.
-/

namespace Exegra.Multiscale

set_option linter.unusedSectionVars false

/-! ### Hierarchy, cut, alpha -/

/-- A relationship as a base fact, with its endpoints resolved to elements. -/
structure Fact (α : Type) where
  id : String
  src : α
  dst : α
  kind : String
  deriving DecidableEq

/-- The fact with its kind coarsened by `κ`. -/
def Fact.mapKind {α : Type} (κ : String → String) (r : Fact α) : Fact α :=
  { r with kind := κ r.kind }

/-- A hierarchy: a parent function and a fuel bound `n` (the ancestor chain has at most `n + 1`
entries). -/
structure Hier (α : Type) where
  parent : α → Option α
  n : Nat

section Generic

variable {α : Type} [DecidableEq α]

/-- The ancestor chain `[e, parent e, parent (parent e), …]`, with fuel. -/
def ancsF (parent : α → Option α) : Nat → α → List α
  | 0, e => [e]
  | n + 1, e => e :: (match parent e with
      | none => []
      | some p => ancsF parent n p)

/-- The ancestors-or-self of `e`. -/
def Hier.ancs (H : Hier α) (e : α) : List α := ancsF H.parent H.n e

theorem ancsF_mem_self (parent : α → Option α) (n : Nat) (e : α) : e ∈ ancsF parent n e := by
  cases n <;> simp [ancsF]

theorem ancsF_mono (parent : α → Option α) :
    ∀ {n m : Nat}, n ≤ m → ∀ e x, x ∈ ancsF parent n e → x ∈ ancsF parent m e
  | 0, m, _, e, x, hx => by
    simp only [ancsF, List.mem_singleton] at hx
    subst hx
    exact ancsF_mem_self parent m x
  | n + 1, 0, h, _, _, _ => by omega
  | n + 1, m + 1, h, e, x, hx => by
    simp only [ancsF, List.mem_cons] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · right
      cases hp : parent e with
      | none => simp [hp] at hx
      | some p =>
        simp only [hp] at hx ⊢
        exact ancsF_mono parent (by omega) p x hx

/-- Two ancestors-or-self of the same element are comparable: one is an ancestor of the other. -/
theorem ancsF_comparable (parent : α → Option α) :
    ∀ (n : Nat) (e x y : α), x ∈ ancsF parent n e → y ∈ ancsF parent n e →
      x ∈ ancsF parent n y ∨ y ∈ ancsF parent n x
  | 0, e, x, y, hx, hy => by
    simp only [ancsF, List.mem_singleton] at hx hy
    subst hx; subst hy
    exact Or.inl (ancsF_mem_self parent 0 _)
  | n + 1, e, x, y, hx, hy => by
    by_cases hxe : x = e
    · subst hxe; exact Or.inr hy
    · by_cases hye : y = e
      · subst hye; exact Or.inl hx
      · have hx' : x ∈ (match parent e with | none => [] | some p => ancsF parent n p) := by
          simp only [ancsF, List.mem_cons] at hx
          rcases hx with h | h
          · exact absurd h hxe
          · exact h
        have hy' : y ∈ (match parent e with | none => [] | some p => ancsF parent n p) := by
          simp only [ancsF, List.mem_cons] at hy
          rcases hy with h | h
          · exact absurd h hye
          · exact h
        cases hp : parent e with
        | none => rw [hp] at hx'; simp at hx'
        | some p =>
          rw [hp] at hx' hy'
          rcases ancsF_comparable parent n p x y hx' hy' with h | h
          · exact Or.inl (ancsF_mono parent (by omega) _ _ h)
          · exact Or.inr (ancsF_mono parent (by omega) _ _ h)

theorem ancsF_trans (parent : α → Option α) :
    ∀ (b a : Nat) (z y x : α), y ∈ ancsF parent b z → x ∈ ancsF parent a y →
      x ∈ ancsF parent (a + b) z
  | 0, a, z, y, x, hy, hx => by
    simp only [ancsF, List.mem_singleton] at hy
    subst hy
    exact hx
  | b + 1, a, z, y, x, hy, hx => by
    simp only [ancsF, List.mem_cons] at hy
    rcases hy with hy | hy
    · subst hy
      exact ancsF_mono parent (by omega) _ _ hx
    · cases hp : parent z with
      | none => rw [hp] at hy; simp at hy
      | some p =>
        rw [hp] at hy
        have := ancsF_trans parent b a p y x hy hx
        show x ∈ ancsF parent (a + b + 1) z
        simp only [ancsF, List.mem_cons]
        right
        rw [hp]
        exact this

/-- A well-formed hierarchy: the ancestor chains are complete within the fuel. -/
def Hier.Stable (H : Hier α) : Prop := ∀ e, ancsF H.parent (H.n + 1) e = ancsF H.parent H.n e

theorem Hier.Stable.ge {H : Hier α} (hs : H.Stable) :
    ∀ (d : Nat) (e : α), ancsF H.parent (H.n + d) e = ancsF H.parent H.n e
  | 0, e => rfl
  | d + 1, e => by
    have key : ancsF H.parent (H.n + d + 1) e = ancsF H.parent (H.n + 1) e := by
      cases hp : H.parent e with
      | none => simp [ancsF, hp]
      | some p =>
        simp only [ancsF, hp]
        rw [Hier.Stable.ge hs d p]
    show ancsF H.parent (H.n + d + 1) e = _
    rw [key, hs e]

/-- The ancestor relation of a well-formed hierarchy is transitive. -/
theorem Hier.Stable.trans {H : Hier α} (hs : H.Stable) {x y z : α}
    (hxy : x ∈ H.ancs y) (hyz : y ∈ H.ancs z) : x ∈ H.ancs z := by
  have := ancsF_trans H.parent H.n H.n z y x hyz hxy
  rw [Hier.Stable.ge hs H.n z] at this
  exact this

theorem Hier.mem_self (H : Hier α) (e : α) : e ∈ H.ancs e := ancsF_mem_self _ _ _

/-- `alpha H C e`: the ancestor-or-self of `e` on the cut `C` (the first block of the ancestor chain),
or `e` itself when the chain meets no block (an element above the cut is its own implicit block). -/
def alpha (H : Hier α) (C : α → Bool) (e : α) : α := ((H.ancs e).find? C).getD e

/-- A cut is an antichain: no block is a strict ancestor of another. -/
def Antichain (H : Hier α) (C : α → Bool) : Prop :=
  ∀ a b, C a = true → C b = true → a ∈ H.ancs b → a = b

/-- `e` is at or below the cut: some ancestor-or-self of `e` is a block. -/
def Below (H : Hier α) (C : α → Bool) (e : α) : Prop := ∃ b ∈ H.ancs e, C b = true

/-- `alpha` is total: it always returns an ancestor-or-self. -/
theorem p1_alpha_total (H : Hier α) (C : α → Bool) (e : α) : alpha H C e ∈ H.ancs e := by
  unfold alpha
  cases h : (H.ancs e).find? C with
  | none => simpa using H.mem_self e
  | some b => simpa using List.mem_of_find?_eq_some h

/-- When `e` is at or below the cut, `alpha` is a block. -/
theorem alpha_spec (H : Hier α) (C : α → Bool) (e : α) (hb : Below H C e) :
    C (alpha H C e) = true := by
  obtain ⟨b, hbm, hbc⟩ := hb
  unfold alpha
  cases h : (H.ancs e).find? C with
  | none => exact absurd hbc (List.find?_eq_none.1 h b hbm)
  | some b' => simpa using List.find?_some h

/-- When `e` meets no block, `alpha` is `e` itself. -/
theorem alpha_of_no_block (H : Hier α) (C : α → Bool) (e : α) (h : ¬ Below H C e) :
    alpha H C e = e := by
  unfold alpha
  cases hf : (H.ancs e).find? C with
  | none => rfl
  | some b' =>
    exact absurd ⟨b', List.mem_of_find?_eq_some hf, List.find?_some hf⟩ h

/-- **P1.** On an antichain cut, if a block `b` is an ancestor-or-self of `e` then it is `alpha C e`:
at most one element of the chain is a block. No hypothesis on the hierarchy is needed. -/
theorem p1_alpha_unique (H : Hier α) (C : α → Bool) (hA : Antichain H C) (e b : α)
    (hb : b ∈ H.ancs e) (hc : C b = true) : alpha H C e = b := by
  have hc' := alpha_spec H C e ⟨b, hb, hc⟩
  have hm := p1_alpha_total H C e
  rcases ancsF_comparable H.parent H.n e _ _ hm hb with h | h
  · exact hA _ _ hc' hc h
  · exact (hA _ _ hc hc' h).symm

/-- Cut `C` refines to `C'`: every block of `C` has an ancestor-or-self that is a block of `C'`. -/
def Refines (H : Hier α) (C C' : α → Bool) : Prop :=
  ∀ b, C b = true → ∃ b' ∈ H.ancs b, C' b' = true

/-- **P2.** Cuts compose: for `C ≤ C'` (`Refines`), `alpha C' e = alpha C' (alpha C e)` for every `e`
at or below `C`. (`alpha_{C→C'}` is `alpha C'` restricted to the blocks of `C`.) Only `C'` needs to be
an antichain. -/
theorem p2_cut_compose (H : Hier α) (hs : H.Stable) (C C' : α → Bool) (hA' : Antichain H C')
    (hr : Refines H C C') (e : α) (he : Below H C e) :
    alpha H C' e = alpha H C' (alpha H C e) := by
  have hb := alpha_spec H C e he
  have hm := p1_alpha_total H C e
  obtain ⟨b', hb'm, hb'c⟩ := hr _ hb
  have h1 : b' ∈ H.ancs e := hs.trans hb'm hm
  rw [p1_alpha_unique H C' hA' e b' h1 hb'c, p1_alpha_unique H C' hA' _ b' hb'm hb'c]

/-! ### Lifting: witnesses, fibres, boundaries -/

/-- The facts whose source block is `X`, target block is `Y` and coarsened kind is `k`, for an
arbitrary block function `a` (the executable part supplies a table-backed `alpha`). -/
def witnessesBy (a : α → α) (κ : String → String) (F : List (Fact α)) (X Y : α) (k : String) :
    List (Fact α) :=
  F.filter (fun r => a r.src == X && a r.dst == Y && κ r.kind == k)

/-- The facts inside block `X`. -/
def fibreBy (a : α → α) (F : List (Fact α)) (X : α) : List (Fact α) :=
  F.filter (fun r => a r.src == X && a r.dst == X)

/-- The facts leaving block `X`. -/
def outBy (a : α → α) (F : List (Fact α)) (X : α) : List (Fact α) :=
  F.filter (fun r => a r.src == X && a r.dst != X)

/-- The facts entering block `X`. -/
def innBy (a : α → α) (F : List (Fact α)) (X : α) : List (Fact α) :=
  F.filter (fun r => a r.dst == X && a r.src != X)

/-- Witnesses of the interaction `(X, Y, k)` at the cut `C`, under the kind map `κ`. -/
def witnesses (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α)) (X Y : α)
    (k : String) : List (Fact α) := witnessesBy (alpha H C) κ F X Y k

def fibre (H : Hier α) (C : α → Bool) (F : List (Fact α)) (X : α) : List (Fact α) :=
  fibreBy (alpha H C) F X

def out (H : Hier α) (C : α → Bool) (F : List (Fact α)) (X : α) : List (Fact α) :=
  outBy (alpha H C) F X

def inn (H : Hier α) (C : α → Bool) (F : List (Fact α)) (X : α) : List (Fact α) :=
  innBy (alpha H C) F X

/-- The interaction `(X, Y, k)` exists iff `X ≠ Y` and its witness list is non-empty. -/
def Interacts (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α)) (X Y : α)
    (k : String) : Prop := X ≠ Y ∧ witnesses H C κ F X Y k ≠ []

/-! ### Summaries -/

/-- A commutative monoid (the summary codomain). -/
class CMon (M : Type) extends Add M, Zero M where
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  add_comm : ∀ a b : M, a + b = b + a
  zero_add : ∀ a : M, 0 + a = a

/-- The summary of a witness list under a per-fact value `h`. -/
def summary {M : Type} [CMon M] (h : Fact α → M) (ws : List (Fact α)) : M :=
  (ws.map h).foldr (· + ·) 0

theorem summary_nil {M : Type} [CMon M] (h : Fact α → M) : summary h [] = 0 := rfl

theorem summary_cons {M : Type} [CMon M] (h : Fact α → M) (r : Fact α) (ws : List (Fact α)) :
    summary h (r :: ws) = h r + summary h ws := rfl

theorem summary_append {M : Type} [CMon M] (h : Fact α → M) (xs ys : List (Fact α)) :
    summary h (xs ++ ys) = summary h xs + summary h ys := by
  induction xs with
  | nil => rw [List.nil_append, summary_nil, CMon.zero_add]
  | cons x xs ih => rw [List.cons_append, summary_cons, summary_cons, ih, CMon.add_assoc]

/-- **P3 (summaries).** A summary is additive over a disjoint split of a list: the coarse summary is
the sum of the finer summaries it unites. -/
theorem p3_summary_hom {M : Type} [CMon M] (h : Fact α → M) (p q : Fact α → Bool)
    (hd : ∀ r, ¬ (p r = true ∧ q r = true)) (F : List (Fact α)) :
    summary h (F.filter (fun r => p r || q r)) = summary h (F.filter p) + summary h (F.filter q) := by
  induction F with
  | nil =>
    simp only [List.filter_nil, summary_nil]
    rw [CMon.zero_add]
  | cons r F ih =>
    cases hp : p r <;> cases hq : q r
    · simp only [List.filter_cons, hp, hq, Bool.or_self]
      simpa using ih
    · simp only [List.filter_cons, hp, hq, Bool.or_true, Bool.false_eq_true, ite_true, ite_false,
        summary_cons]
      rw [ih, ← CMon.add_assoc, CMon.add_comm (h r) (summary h (F.filter p)), CMon.add_assoc]
    · simp only [List.filter_cons, hp, hq, Bool.true_or, Bool.false_eq_true, ite_true, ite_false,
        summary_cons]
      rw [ih, CMon.add_assoc]
    · exact absurd ⟨hp, hq⟩ (hd r)

/-! ### P3: lift functoriality -/

/-- **P3.** Lifting at `C` and then at `C' ≥ C` is lifting at `C'`: for `X ≠ Y`, the witnesses at `C'`
of `(X, Y, k)` under `κ' ∘ κ` are the facts that cross two distinct blocks of `C` lying in `X` and
`Y` and whose `κ' (κ kind)` is `k`. -/
theorem p3_lift_functorial (H : Hier α) (hs : H.Stable) (C C' : α → Bool) (hA' : Antichain H C')
    (hr : Refines H C C') (κ κ' : String → String) (F : List (Fact α))
    (hF : ∀ r ∈ F, Below H C r.src ∧ Below H C r.dst) (X Y : α) (hXY : X ≠ Y) (k : String) :
    witnesses H C' (κ' ∘ κ) F X Y k =
      F.filter (fun r => alpha H C r.src != alpha H C r.dst &&
        alpha H C' (alpha H C r.src) == X && alpha H C' (alpha H C r.dst) == Y &&
        κ' (κ r.kind) == k) := by
  unfold witnesses witnessesBy
  apply List.filter_congr
  intro r hrm
  obtain ⟨h1, h2⟩ := hF r hrm
  rw [p2_cut_compose H hs C C' hA' hr _ h1, p2_cut_compose H hs C C' hA' hr _ h2]
  simp only [Function.comp_apply]
  by_cases a1 : alpha H C' (alpha H C r.src) = X
  · by_cases a2 : alpha H C' (alpha H C r.dst) = Y
    · have hne : (alpha H C r.src != alpha H C r.dst) = true := by
        rw [bne_iff_ne]
        intro heq
        apply hXY
        rw [← a1, ← a2, heq]
      simp [a1, hne]
    · have a2' : (alpha H C' (alpha H C r.dst) == Y) = false := beq_false_of_ne a2
      simp [a1, a2']
  · have a1' : (alpha H C' (alpha H C r.src) == X) = false := beq_false_of_ne a1
    simp [a1']

/-- **P3 (kind coarsening composes).** Lifting with `κ` and then coarsening the kinds of the result with
`κ'` is lifting with `κ' ∘ κ` (the facts differ only by the kind rewrite). -/
theorem p3_coarsen_compose (H : Hier α) (C : α → Bool) (κ κ' : String → String) (F : List (Fact α))
    (X Y : α) (k : String) :
    witnesses H C κ' (F.map (Fact.mapKind κ)) X Y k =
      (witnesses H C (κ' ∘ κ) F X Y k).map (Fact.mapKind κ) := by
  unfold witnesses witnessesBy
  rw [List.filter_map]
  congr 1

/-- **P3 (kind classes unite).** A witness at the coarse kind `k` is exactly a witness at some finer
kind `k'` that coarsens to `k`. -/
theorem p3_coarsen_union (H : Hier α) (C : α → Bool) (κ κ' : String → String) (F : List (Fact α))
    (X Y : α) (k : String) (r : Fact α) :
    r ∈ witnesses H C (κ' ∘ κ) F X Y k ↔
      ∃ k', κ' k' = k ∧ r ∈ witnesses H C κ F X Y k' := by
  unfold witnesses witnessesBy
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, Function.comp_apply]
  constructor
  · rintro ⟨hm, ⟨h1, h2⟩, h3⟩
    exact ⟨κ r.kind, h3, hm, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨k', hk', hm, ⟨h1, h2⟩, h3⟩
    exact ⟨hm, ⟨h1, h2⟩, by rw [h3, hk']⟩

/-! ### P4: absence transfers up -/

/-- **P4.** An interaction with an empty witness list excludes every base fact of that key. -/
theorem p4_absence_transfer (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α))
    (X Y : α) (k : String) (h : witnesses H C κ F X Y k = []) :
    ∀ r ∈ F, ¬ (alpha H C r.src = X ∧ alpha H C r.dst = Y ∧ κ r.kind = k) := by
  unfold witnesses witnessesBy at h
  intro r hr hc
  have := List.filter_eq_nil_iff.1 h r hr
  simp [hc.1, hc.2.1, hc.2.2] at this

/-- **P4 (kind classes).** If the witness list is empty for every kind of class `c`, no base fact from a
member of `X` to a member of `Y` has class `c`. -/
theorem p4_absence_class (H : Hier α) (C : α → Bool) (κ cls : String → String) (F : List (Fact α))
    (X Y : α) (c : String) (h : ∀ k, cls k = c → witnesses H C κ F X Y k = []) :
    ∀ r ∈ F, ¬ (alpha H C r.src = X ∧ alpha H C r.dst = Y ∧ cls (κ r.kind) = c) := by
  intro r hr hc
  exact p4_absence_transfer H C κ F X Y (κ r.kind) (h _ hc.2.2) r hr ⟨hc.1, hc.2.1, rfl⟩

/-! ### P5: interfaces and boundaries -/

/-- Direction of a boundary fact. -/
inductive Dir where
  | out
  | inn
  deriving DecidableEq

/-- The boundary facts of one direction grouped by kind: each distinct kind, in order of first
appearance, with its facts. -/
def group (d : Dir) (bs : List (Fact α)) : List (Dir × String × List (Fact α)) :=
  (bs.map (·.kind)).eraseDups.map (fun k => (d, k, bs.filter (fun r => r.kind == k)))

/-- The derived interface: a function of the two boundary lists only. -/
def iface (o i : List (Fact α)) : List (Dir × String × List (Fact α)) :=
  group Dir.out o ++ group Dir.inn i

/-- The interface of block `X` at cut `C`. -/
def interface (H : Hier α) (C : α → Bool) (F : List (Fact α)) (X : α) :
    List (Dir × String × List (Fact α)) :=
  iface (out H C F X) (inn H C F X)

/-- **P5.** Two blocks (of two cuts, or two fact bases) with the same boundary have the same interface. -/
theorem p5_boundary_determines_interface (H H' : Hier α) (C C' : α → Bool) (F F' : List (Fact α))
    (X X' : α) (ho : out H C F X = out H' C' F' X') (hi : inn H C F X = inn H' C' F' X') :
    interface H C F X = interface H' C' F' X' := by
  unfold interface
  rw [ho, hi]

/-- **P5.** The boundary of a coarse block is the boundary of its members that leaves it: for `C ≤ C'`
and every endpoint at or below `C`, `out C' F X` is the facts of `F` in `out C F x` for the block `x`
of their source, with `x` in `X` and the target's `C'`-block not `X`. -/
theorem p5_boundary_compose (H : Hier α) (hs : H.Stable) (C C' : α → Bool) (hA' : Antichain H C')
    (hr : Refines H C C') (F : List (Fact α))
    (hF : ∀ r ∈ F, Below H C r.src ∧ Below H C r.dst) (X : α) :
    out H C' F X =
      F.filter (fun r => alpha H C' (alpha H C r.src) == X && alpha H C r.dst != alpha H C r.src &&
        alpha H C' (alpha H C r.dst) != X) := by
  unfold out outBy
  apply List.filter_congr
  intro r hrm
  obtain ⟨h1, h2⟩ := hF r hrm
  rw [p2_cut_compose H hs C C' hA' hr _ h1, p2_cut_compose H hs C C' hA' hr _ h2]
  by_cases a1 : alpha H C' (alpha H C r.src) = X
  · by_cases a2 : alpha H C' (alpha H C r.dst) = X
    · simp [a1, a2]
    · have hne : (alpha H C r.dst != alpha H C r.src) = true := by
        rw [bne_iff_ne]
        intro heq
        apply a2
        rw [heq, a1]
      simp [a1, hne]
  · have a1' : (alpha H C' (alpha H C r.src) == X) = false := beq_false_of_ne a1
    simp [a1']

/-- Symmetric to `p5_boundary_compose`: the incoming boundary. -/
theorem p5_boundary_compose_in (H : Hier α) (hs : H.Stable) (C C' : α → Bool)
    (hA' : Antichain H C') (hr : Refines H C C') (F : List (Fact α))
    (hF : ∀ r ∈ F, Below H C r.src ∧ Below H C r.dst) (X : α) :
    inn H C' F X =
      F.filter (fun r => alpha H C' (alpha H C r.dst) == X && alpha H C r.src != alpha H C r.dst &&
        alpha H C' (alpha H C r.src) != X) := by
  unfold inn innBy
  apply List.filter_congr
  intro r hrm
  obtain ⟨h1, h2⟩ := hF r hrm
  rw [p2_cut_compose H hs C C' hA' hr _ h1, p2_cut_compose H hs C C' hA' hr _ h2]
  by_cases a1 : alpha H C' (alpha H C r.dst) = X
  · by_cases a2 : alpha H C' (alpha H C r.src) = X
    · simp [a1, a2]
    · have hne : (alpha H C r.src != alpha H C r.dst) = true := by
        rw [bne_iff_ne]
        intro heq
        apply a2
        rw [heq, a1]
      simp [a1, hne]
  · have a1' : (alpha H C' (alpha H C r.dst) == X) = false := beq_false_of_ne a1
    simp [a1']

/-! ### P6: paths -/

/-- Reflexive-transitive closure. -/
inductive RTG {β : Type} (R : β → β → Prop) : β → β → Prop where
  | refl (a : β) : RTG R a a
  | tail {a b c : β} : RTG R a b → R b c → RTG R a c

/-- Transitive closure. -/
inductive TG {β : Type} (R : β → β → Prop) : β → β → Prop where
  | single {a b : β} : R a b → TG R a b
  | tail {a b c : β} : TG R a b → R b c → TG R a c

theorem RTG.of_TG {β : Type} {R : β → β → Prop} {a b : β} (h : TG R a b) : RTG R a b := by
  induction h with
  | single h => exact RTG.tail (RTG.refl _) h
  | tail _ h ih => exact RTG.tail ih h

theorem TG.of_RTG_ne {β : Type} {R : β → β → Prop} {a b : β} (h : RTG R a b) (hne : a ≠ b) :
    TG R a b := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail b c _ hbc ih =>
    by_cases hab : a = b
    · subst hab; exact TG.single hbc
    · exact TG.tail (ih hab) hbc

theorem TG.of_TG_RTG {β : Type} {R : β → β → Prop} {a b c : β} (h : TG R a b) (h2 : RTG R b c) :
    TG R a c := by
  induction h2 with
  | refl => exact h
  | tail _ hr ih => exact TG.tail ih hr

/-- The base edge relation of a fact base. -/
def Edge (F : List (Fact α)) (a b : α) : Prop := ∃ r ∈ F, r.src = a ∧ r.dst = b

/-- The quotient relation: an edge between distinct blocks with a witness (of some kind). -/
def Qrel (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α)) (X Y : α) : Prop :=
  X ≠ Y ∧ ∃ k, witnesses H C κ F X Y k ≠ []

/-- **P6.** A base path lifts to a coarse path between the blocks of its ends. -/
theorem p6_reach_up (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α)) {a b : α}
    (h : RTG (Edge F) a b) : RTG (Qrel H C κ F) (alpha H C a) (alpha H C b) := by
  induction h with
  | refl => exact RTG.refl _
  | @tail m b _ hmb ih =>
    obtain ⟨r, hr, hs, hd⟩ := hmb
    by_cases heq : alpha H C m = alpha H C b
    · rw [← heq]; exact ih
    · refine RTG.tail ih ⟨heq, κ r.kind, ?_⟩
      intro hnil
      have hmem : r ∈ witnesses H C κ F (alpha H C m) (alpha H C b) (κ r.kind) := by
        unfold witnesses witnessesBy
        rw [List.mem_filter]
        refine ⟨hr, ?_⟩
        simp [hs, hd]
      rw [hnil] at hmem
      exact List.not_mem_nil hmem

/-- **P6.** If the quotient relation is acyclic, a base cycle lies inside one block: a non-empty path
from `a` to `b` and a path back from `b` to `a` force `alpha a = alpha b`. -/
theorem p6_acyclic_down (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α))
    (hac : ∀ X, ¬ TG (Qrel H C κ F) X X) {a b : α} (hab : TG (Edge F) a b)
    (hba : RTG (Edge F) b a) : alpha H C a = alpha H C b := by
  refine Classical.byContradiction fun hne => ?_
  have h1 := p6_reach_up H C κ F (RTG.of_TG hab)
  have h2 := p6_reach_up H C κ F hba
  exact hac _ (TG.of_TG_RTG (TG.of_RTG_ne h1 hne) h2)

/-! #### The converse fails: a spurious coarse path -/

/-- Blocks `10 = {1, 2}`, `20 = {3, 4}`, `30 = {5, 6}`. -/
def exParent : Nat → Option Nat
  | 1 => some 10 | 2 => some 10 | 3 => some 20 | 4 => some 20 | 5 => some 30 | 6 => some 30
  | _ => none

def exH : Hier Nat := ⟨exParent, 3⟩

def exC (b : Nat) : Bool := b == 10 || b == 20 || b == 30

def exElems : List Nat := [1, 2, 3, 4, 5, 6, 10, 20, 30]

/-- `1 → 3` (from block 10 to block 20) and `4 → 5` (from block 20 to block 30). -/
def exF : List (Fact Nat) := [⟨"r1", 1, 3, "k"⟩, ⟨"r2", 4, 5, "k"⟩]

/-- **P6.** The quotient has a path `10 → 20 → 30` but no base path leads from any member of block 10
to any member of block 30. -/
theorem p6_spurious_path :
    Qrel exH exC id exF 10 20 ∧ Qrel exH exC id exF 20 30 ∧
    ∀ a ∈ exElems, ∀ b ∈ exElems, alpha exH exC a = 10 → alpha exH exC b = 30 →
      ¬ RTG (Edge exF) a b := by
  refine ⟨⟨by decide, "k", by decide⟩, ⟨by decide, "k", by decide⟩, ?_⟩
  intro a ha b hb hab hbb hp
  have hA : ∀ a ∈ exElems, alpha exH exC a = 10 → a ∈ [1, 2, 10, 3] := by decide
  have hB : ∀ b ∈ exElems, alpha exH exC b = 30 → b ∈ [1, 2, 10, 3] → False := by decide
  have hinv : ∀ y, RTG (Edge exF) a y → y ∈ [1, 2, 10, 3] := by
    intro y hy
    induction hy with
    | refl => exact hA a ha hab
    | @tail m y _ hmy ih =>
      obtain ⟨r, hr, hs, hd⟩ := hmy
      simp only [exF, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only at hs hd
        subst hd; simp
      · simp only at hs hd
        subst hs
        simp at ih
  exact hB b hb hbb (hinv b hp)

/-! ### P7: decomposition recovers the fact base -/

/-- **P7.** Every fact is in the fibre of its block (when its ends share a block) or in the witness list
of exactly its key (when they do not), and conversely. -/
theorem p7_recover (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α))
    (r : Fact α) :
    r ∈ F ↔ (alpha H C r.src = alpha H C r.dst ∧ r ∈ fibre H C F (alpha H C r.src)) ∨
            (alpha H C r.src ≠ alpha H C r.dst ∧
              r ∈ witnesses H C κ F (alpha H C r.src) (alpha H C r.dst) (κ r.kind)) := by
  unfold fibre fibreBy witnesses witnessesBy
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    by_cases heq : alpha H C r.src = alpha H C r.dst
    · left; simp [heq, h]
    · right; simp [heq, h]
  · intro h
    rcases h with h | h <;> simp_all

/-- **P7.** A fact in a fibre belongs to it by its own block: the fibre of exactly one block. -/
theorem p7_unique_fibre (H : Hier α) (C : α → Bool) (F : List (Fact α)) (X : α) (r : Fact α)
    (h : r ∈ fibre H C F X) : alpha H C r.src = X ∧ alpha H C r.dst = X := by
  unfold fibre fibreBy at h
  simpa using (List.mem_filter.1 h).2

/-- **P7.** A fact in a witness list belongs to it by its own key: the list of exactly one interaction. -/
theorem p7_unique_key (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α))
    (X Y : α) (k : String) (r : Fact α) (h : r ∈ witnesses H C κ F X Y k) :
    alpha H C r.src = X ∧ alpha H C r.dst = Y ∧ κ r.kind = k := by
  unfold witnesses witnessesBy at h
  have := (List.mem_filter.1 h).2
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **P7.** No fact is in a fibre and in the witness list of an interaction between distinct blocks. -/
theorem p7_exclusive (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α))
    (X X' Y : α) (k : String) (hXY : X' ≠ Y) (r : Fact α) (h1 : r ∈ fibre H C F X)
    (h2 : r ∈ witnesses H C κ F X' Y k) : False := by
  obtain ⟨a, b⟩ := p7_unique_fibre H C F X r h1
  obtain ⟨c, d, _⟩ := p7_unique_key H C κ F X' Y k r h2
  exact hXY (by rw [← c, ← d, a, b])

/-- **P7.** Everything in a fibre or a witness list is in `F`. -/
theorem p7_sub (H : Hier α) (C : α → Bool) (κ : String → String) (F : List (Fact α)) (X Y : α)
    (k : String) :
    (∀ r, r ∈ fibre H C F X → r ∈ F) ∧ (∀ r, r ∈ witnesses H C κ F X Y k → r ∈ F) := by
  unfold fibre fibreBy witnesses witnessesBy
  exact ⟨fun r h => (List.mem_filter.1 h).1, fun r h => (List.mem_filter.1 h).1⟩

/-! ### P13: incremental re-derivation equals full -/

/-- A fact is in exactly one of the two bases. -/
def Changed (F F' : List (Fact α)) (r : Fact α) : Prop := (r ∈ F ∧ r ∉ F') ∨ (r ∈ F' ∧ r ∉ F)

/-- Incremental re-derivation of a witness table: recompute dirty keys, keep the previous value
elsewhere. -/
def incr (D : α → α → String → Bool) (prev W' : α → α → String → List (Fact α)) (X Y : α)
    (k : String) : List (Fact α) :=
  if D X Y k = true then W' X Y k else prev X Y k

/-- Incremental re-derivation of a fibre table. -/
def incrFibre (D : α → Bool) (prev W' : α → List (Fact α)) (X : α) : List (Fact α) :=
  if D X = true then W' X else prev X

/-- **P13.** With `D` containing the key of every fact that is in one base and not the other, the
incrementally re-derived witnesses have the same members as the full derivation, at every key. -/
theorem p13_incremental (H : Hier α) (C : α → Bool) (κ : String → String) (F F' : List (Fact α))
    (D : α → α → String → Bool)
    (hD : ∀ r, Changed F F' r → D (alpha H C r.src) (alpha H C r.dst) (κ r.kind) = true)
    (prev : α → α → String → List (Fact α))
    (hprev : ∀ X Y k, prev X Y k = witnesses H C κ F X Y k) (X Y : α) (k : String) (r : Fact α) :
    r ∈ incr D prev (witnesses H C κ F') X Y k ↔ r ∈ witnesses H C κ F' X Y k := by
  unfold incr
  by_cases hd : D X Y k = true
  · simp only [hd, ↓reduceIte]
  · have hd' : D X Y k = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, ↓reduceIte]
    rw [hprev]
    unfold witnesses witnessesBy
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨hrF, hk⟩
      refine ⟨?_, hk⟩
      refine Classical.byContradiction fun hn => ?_
      have := hD r (Or.inl ⟨hrF, hn⟩)
      rw [hk.1.1, hk.1.2, hk.2] at this
      exact hd this
    · rintro ⟨hrF, hk⟩
      refine ⟨?_, hk⟩
      refine Classical.byContradiction fun hn => ?_
      have := hD r (Or.inr ⟨hrF, hn⟩)
      rw [hk.1.1, hk.1.2, hk.2] at this
      exact hd this

theorem filter_incr (p keep : Fact α → Bool) (F new : List (Fact α))
    (h1 : ∀ r ∈ F, p r = true → keep r = true) (h2 : ∀ r ∈ new, p r = false) :
    (F.filter keep ++ new).filter p = F.filter p := by
  rw [List.filter_append, List.filter_filter]
  have : new.filter p = [] := List.filter_eq_nil_iff.2 (fun r hr => by simp [h2 r hr])
  rw [this, List.append_nil]
  apply List.filter_congr
  intro r hr
  cases hp : p r
  · simp
  · simp [h1 r hr hp]

/-- **P13 (lists).** When `F'` is `F` with some facts removed and some appended, and `D` contains the
key of every removed or appended fact, the incrementally re-derived witness list equals the full one
(as lists, order included). -/
theorem p13_incremental_list (H : Hier α) (C : α → Bool) (κ : String → String)
    (F new : List (Fact α)) (keep : Fact α → Bool) (D : α → α → String → Bool)
    (hD : ∀ r, ((r ∈ F ∧ keep r = false) ∨ r ∈ new) →
      D (alpha H C r.src) (alpha H C r.dst) (κ r.kind) = true)
    (prev : α → α → String → List (Fact α))
    (hprev : ∀ X Y k, prev X Y k = witnesses H C κ F X Y k) (X Y : α) (k : String) :
    incr D prev (witnesses H C κ (F.filter keep ++ new)) X Y k =
      witnesses H C κ (F.filter keep ++ new) X Y k := by
  unfold incr
  by_cases hd : D X Y k = true
  · simp only [hd, ↓reduceIte]
  · have hd' : D X Y k = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, ↓reduceIte]
    rw [hprev]
    unfold witnesses witnessesBy
    symm
    apply filter_incr
    · intro r hr hp
      refine Classical.byContradiction fun hk => ?_
      have hk' : keep r = false := by simpa using hk
      have := hD r (Or.inl ⟨hr, hk'⟩)
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      rw [hp.1.1, hp.1.2, hp.2] at this
      exact hd this
    · intro r hr
      refine Classical.byContradiction fun hp => ?_
      have hp' : (alpha H C r.src == X && alpha H C r.dst == Y && κ r.kind == k) = true := by
        revert hp
        cases (alpha H C r.src == X && alpha H C r.dst == Y && κ r.kind == k) <;> simp
      have := hD r (Or.inr hr)
      simp only [Bool.and_eq_true, beq_iff_eq] at hp'
      rw [hp'.1.1, hp'.1.2, hp'.2] at this
      exact hd this

/-- **P13 (fibres).** The same for fibres: `D` need contain only the blocks of changed facts that lie
inside one block. -/
theorem p13_incremental_fibre (H : Hier α) (C : α → Bool) (F F' : List (Fact α)) (D : α → Bool)
    (hD : ∀ r, Changed F F' r → alpha H C r.src = alpha H C r.dst → D (alpha H C r.src) = true)
    (prev : α → List (Fact α)) (hprev : ∀ X, prev X = fibre H C F X) (X : α) (r : Fact α) :
    r ∈ incrFibre D prev (fibre H C F') X ↔ r ∈ fibre H C F' X := by
  unfold incrFibre
  by_cases hd : D X = true
  · simp only [hd, ↓reduceIte]
  · have hd' : D X = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, ↓reduceIte]
    rw [hprev]
    unfold fibre fibreBy
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨hrF, hk⟩
      refine ⟨?_, hk⟩
      refine Classical.byContradiction fun hn => ?_
      have := hD r (Or.inl ⟨hrF, hn⟩) (by rw [hk.1, hk.2])
      rw [hk.1] at this
      exact hd this
    · rintro ⟨hrF, hk⟩
      refine ⟨?_, hk⟩
      refine Classical.byContradiction fun hn => ?_
      have := hD r (Or.inr ⟨hrF, hn⟩) (by rw [hk.1, hk.2])
      rw [hk.1] at this
      exact hd this

/-- **P13 (fibres, lists).** As `p13_incremental_list`, for fibres. -/
theorem p13_incremental_fibre_list (H : Hier α) (C : α → Bool) (F new : List (Fact α))
    (keep : Fact α → Bool) (D : α → Bool)
    (hD : ∀ r, ((r ∈ F ∧ keep r = false) ∨ r ∈ new) → alpha H C r.src = alpha H C r.dst →
      D (alpha H C r.src) = true)
    (prev : α → List (Fact α)) (hprev : ∀ X, prev X = fibre H C F X) (X : α) :
    incrFibre D prev (fibre H C (F.filter keep ++ new)) X =
      fibre H C (F.filter keep ++ new) X := by
  unfold incrFibre
  by_cases hd : D X = true
  · simp only [hd, ↓reduceIte]
  · have hd' : D X = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, ↓reduceIte]
    rw [hprev]
    unfold fibre fibreBy
    symm
    apply filter_incr
    · intro r hr hp
      refine Classical.byContradiction fun hk => ?_
      have hk' : keep r = false := by simpa using hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have := hD r (Or.inl ⟨hr, hk'⟩) (by rw [hp.1, hp.2])
      rw [hp.1] at this
      exact hd this
    · intro r hr
      refine Classical.byContradiction fun hp => ?_
      have hp' : (alpha H C r.src == X && alpha H C r.dst == X) = true := by
        revert hp
        cases (alpha H C r.src == X && alpha H C r.dst == X) <;> simp
      simp only [Bool.and_eq_true, beq_iff_eq] at hp'
      have := hD r (Or.inr hr) (by rw [hp'.1, hp'.2])
      rw [hp'.1] at this
      exact hd this

end Generic

/-! ### Executable entry point -/

section Exec

/-- A member of a JSON object. -/
def field? (v : Value) (k : String) : Option Value :=
  match v with
  | .obj _ fs => objGet? fs k
  | _ => none

def items (v : Option Value) : List Value :=
  match v with
  | some (.arr _ xs) => xs
  | _ => []

def jo (fs : List (String × Value)) : Value := .obj 0 fs
def ja (xs : List Value) : Value := .arr 0 xs
def js (x : String) : Value := .str x

/-- Strings in ascending order (code point order, as `<` on ASCII ids in JavaScript). -/
def sortStr (xs : List String) : List String :=
  xs.mergeSort (fun a b => !(decide (b < a)))

/-- Distinct strings, in order of first appearance. -/
def dedupe (xs : List String) : List String :=
  (xs.foldl (fun (acc : Std.HashSet String × List String) x =>
    if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) ({}, [])).2.reverse

/-- The decoded input of `deriveValue`. -/
structure Input where
  elems : List (String × Option String)
  blocks : List String
  facts : List (Fact String)
  coarsen : List (String × String)

def parseInput (args : Value) : Except String Input := do
  match args with
  | .obj .. => pure ()
  | _ => throw "multiscale.derive: the argument must be an object"
  let str (what : String) (v : Option Value) : Except String String :=
    match v with
    | some (.str s) => pure s
    | _ => throw s!"multiscale.derive: {what} must be a string"
  let elems ← (items (field? args "elements")).mapM fun e => do
    let id ← str "an element \"id\"" (field? e "id")
    let p := match field? e "parent" with
      | some (.str s) => some s
      | _ => none
    pure (id, p)
  let blocks ← (items (field? args "blocks")).mapM fun b => str "a block" (some b)
  let facts ← (items (field? args "facts")).mapM fun f => do
    let id ← str "a fact \"id\"" (field? f "id")
    let src ← str "a fact \"from\"" (field? f "from")
    let dst ← str "a fact \"to\"" (field? f "to")
    let kind ← str "a fact \"kind\"" (field? f "kind")
    pure ({ id, src, dst, kind } : Fact String)
  let coarsen ← (items (field? args "coarsen")).mapM fun p => do
    match p with
    | .arr _ [.str a, .str b] => pure (a, b)
    | _ => throw "multiscale.derive: a \"coarsen\" entry must be [kind, coarseKind]"
  pure { elems, blocks, facts, coarsen }

/-- The derived model at the cut, as JSON text. -/
def derive (inp : Input) : String :=
  let elemSet : Std.HashSet String := inp.elems.foldl (fun s e => s.insert e.1) {}
  let parentMap : Std.HashMap String String :=
    inp.elems.foldl (fun m e => match e.2 with | some q => m.insert e.1 q | none => m) {}
  let blockSet : Std.HashSet String := inp.blocks.foldl (fun s b => s.insert b) {}
  let H : Hier String := ⟨fun e => parentMap[e]?, inp.elems.length⟩
  let C : String → Bool := fun b => blockSet.contains b
  let κm : Std.HashMap String String := inp.coarsen.foldl (fun m p => m.insert p.1 p.2) {}
  let κ : String → String := fun k => κm.getD k k
  let isPlaced (r : Fact String) : Bool := elemSet.contains r.src && elemSet.contains r.dst
  let placed := inp.facts.filter isPlaced
  let unplaced := sortStr ((inp.facts.filter (fun r => !isPlaced r)).map (·.id))
  -- `alpha` of every placed endpoint, computed once
  let tbl : Std.HashMap String String := placed.foldl (fun m r =>
    let m := if m.contains r.src then m else m.insert r.src (alpha H C r.src)
    if m.contains r.dst then m else m.insert r.dst (alpha H C r.dst)) {}
  let a : String → String := fun e => tbl.getD e e
  let blocks := sortStr (dedupe (inp.blocks ++ (placed.flatMap fun r => [a r.src, a r.dst])))
  let ids (ws : List (Fact String)) : Value := ja ((sortStr (ws.map (·.id))).map js)
  -- distinct interaction keys
  let keys : List (String × String × String × String) :=
    (placed.foldl (fun (acc : Std.HashSet String × List (String × String × String × String)) r =>
      let X := a r.src
      let Y := a r.dst
      let k := κ r.kind
      let ks := s!"{X}->{Y}:{k}"
      if X == Y || acc.1.contains ks then acc else (acc.1.insert ks, (ks, X, Y, k) :: acc.2))
      ({}, [])).2
  let keys := keys.mergeSort (fun p q => !(decide (q.1 < p.1)))
  let interactions := keys.map fun (_, X, Y, k) =>
    jo [("from", js X), ("to", js Y), ("kind", js k),
        ("witnesses", ids (witnessesBy a κ placed X Y k))]
  let fibres := blocks.map fun X => (X, ids (fibreBy a placed X))
  let boundaries := blocks.map fun X =>
    (X, jo [("out", ids (outBy a placed X)), ("in", ids (innBy a placed X))])
  Json.write (jo [("interactions", ja interactions), ("fibres", jo fibres),
    ("boundaries", jo boundaries), ("unplaced", ja (unplaced.map js))])

/-- `{elements, blocks, facts, coarsen?}` to the derived model: interactions, fibres, boundaries and
the unplaced facts, from the same definitions the theorems are about. -/
def deriveValue (args : Value) : Except String String := do
  let inp ← parseInput args
  pure (derive inp)

end Exec

/-! ### Smoke test of the executable part -/

#guard (((match Json.parse "{\"elements\":[{\"id\":\"top\",\"parent\":null},{\"id\":\"m1\",\"parent\":\"top\"},{\"id\":\"m2\",\"parent\":\"top\"},{\"id\":\"a\",\"parent\":\"m1\"},{\"id\":\"b\",\"parent\":\"m1\"},{\"id\":\"c\",\"parent\":\"m2\"}],\"blocks\":[\"m1\",\"m2\"],\"facts\":[{\"id\":\"r2\",\"from\":\"a\",\"to\":\"c\",\"kind\":\"calls\"},{\"id\":\"r1\",\"from\":\"b\",\"to\":\"c\",\"kind\":\"invokes\"},{\"id\":\"r3\",\"from\":\"a\",\"to\":\"b\",\"kind\":\"calls\"},{\"id\":\"r4\",\"from\":\"top\",\"to\":\"m1\",\"kind\":\"x\"},{\"id\":\"r5\",\"from\":\"a\",\"to\":\"zz\",\"kind\":\"x\"}],\"coarsen\":[[\"invokes\",\"calls\"]]}" with | .ok v => v | .error _ => .null) |> deriveValue).toOption == some "{\"interactions\":[{\"from\":\"m1\",\"to\":\"m2\",\"kind\":\"calls\",\"witnesses\":[\"r1\",\"r2\"]},{\"from\":\"top\",\"to\":\"m1\",\"kind\":\"x\",\"witnesses\":[\"r4\"]}],\"fibres\":{\"m1\":[\"r3\"],\"m2\":[],\"top\":[]},\"boundaries\":{\"m1\":{\"out\":[\"r1\",\"r2\"],\"in\":[\"r4\"]},\"m2\":{\"out\":[],\"in\":[\"r1\",\"r2\"]},\"top\":{\"out\":[\"r4\"],\"in\":[]}},\"unplaced\":[\"r5\"]}")

/-! ### Axioms: only the standard ones -/

/-- info: 'Exegra.Multiscale.p1_alpha_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p1_alpha_unique

/-- info: 'Exegra.Multiscale.p1_alpha_total' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p1_alpha_total

/-- info: 'Exegra.Multiscale.alpha_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.alpha_spec

/-- info: 'Exegra.Multiscale.alpha_of_no_block' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.alpha_of_no_block

/-- info: 'Exegra.Multiscale.p2_cut_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p2_cut_compose

/-- info: 'Exegra.Multiscale.p3_lift_functorial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p3_lift_functorial

/-- info: 'Exegra.Multiscale.p3_summary_hom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p3_summary_hom

/-- info: 'Exegra.Multiscale.summary_append' does not depend on any axioms -/
#guard_msgs in
#print axioms Exegra.Multiscale.summary_append

/-- info: 'Exegra.Multiscale.p3_coarsen_compose' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p3_coarsen_compose

/-- info: 'Exegra.Multiscale.p3_coarsen_union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p3_coarsen_union

/-- info: 'Exegra.Multiscale.p4_absence_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p4_absence_transfer

/-- info: 'Exegra.Multiscale.p4_absence_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p4_absence_class

/-- info: 'Exegra.Multiscale.p5_boundary_determines_interface' does not depend on any axioms -/
#guard_msgs in
#print axioms Exegra.Multiscale.p5_boundary_determines_interface

/-- info: 'Exegra.Multiscale.p5_boundary_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p5_boundary_compose

/-- info: 'Exegra.Multiscale.p5_boundary_compose_in' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p5_boundary_compose_in

/-- info: 'Exegra.Multiscale.p6_reach_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p6_reach_up

/-- info: 'Exegra.Multiscale.p6_acyclic_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p6_acyclic_down

/-- info: 'Exegra.Multiscale.p6_spurious_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p6_spurious_path

/-- info: 'Exegra.Multiscale.p7_recover' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p7_recover

/-- info: 'Exegra.Multiscale.p7_unique_fibre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p7_unique_fibre

/-- info: 'Exegra.Multiscale.p7_unique_key' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p7_unique_key

/-- info: 'Exegra.Multiscale.p7_exclusive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p7_exclusive

/-- info: 'Exegra.Multiscale.p7_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p7_sub

/-- info: 'Exegra.Multiscale.p13_incremental' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p13_incremental

/-- info: 'Exegra.Multiscale.p13_incremental_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p13_incremental_list

/-- info: 'Exegra.Multiscale.p13_incremental_fibre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p13_incremental_fibre

/-- info: 'Exegra.Multiscale.p13_incremental_fibre_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Multiscale.p13_incremental_fibre_list

end Exegra.Multiscale
