import Exegra.Core.Behav

/-
Renaming machines (plan-M2; the task's criterion 8, "one verdict, in general").

A permutation `π` of the machine indices lists the machines of a system in another order:
`Sys.rename π` moves machine `π.g m'` to position `m'` (so machine `m` goes to `π.f m`), renames
every reference to a machine (other machines' variables and control states, aggregates over
instances, the targets and senders of entries, the transitions an `enable`/`disable` fault targets,
the machine of a sampled delay) and permutes the machine list of the initial configuration.
`State.rename π` does the same to a state.

`invariant_rename`: for every property `P` that does not depend on the order of the pending list,
`P` is an invariant of a system exactly when `P ∘ State.rename π⁻¹` is an invariant of the system
listed in the order `π`. So the verdict of a safety property does not depend on the order in which
the machines are listed: the `[a, b]` / `[b, a]` examples of `BehavExamples.lean` are instances.

A renaming acts on configurations whose machine list has the signature's length (every
configuration of a well-formed system: `Cfg.Shaped`); on a system whose initial configuration has
another number of machines `Sys.rename` is the identity, and so is `State.rename` on a state of
another length, so the theorem needs no hypothesis.

The proof is a bisimulation up to a permutation of the pending list: a step of the system is a step
of the renamed system from the renamed state, with the renamed label, to a state equal to the
renamed successor up to the order of its pending list, and conversely. The order of the winners and
of the emitted entries changes with the listing; `deliver_perm`'s lemmas (`afterPhase2_perm`) and
`pending_perm_bisim` absorb it.
-/

namespace Exegra.Core.Behav

open Exegra.Core.LTS

/-! ### Permutations of the machine indices -/

/-- A permutation of the machine indices `Fin n`, with its inverse. -/
structure MPerm (n : Nat) where
  f : Fin n → Fin n
  g : Fin n → Fin n
  gf : ∀ x, g (f x) = x
  fg : ∀ x, f (g x) = x

instance {n : Nat} : Inv (MPerm n) := ⟨fun π => ⟨π.g, π.f, π.fg, π.gf⟩⟩

namespace MPerm

variable {n : Nat} (π : MPerm n)

@[simp] theorem inv_f : (π⁻¹).f = π.g := rfl
@[simp] theorem inv_g : (π⁻¹).g = π.f := rfl
@[simp] theorem inv_inv : (π⁻¹)⁻¹ = π := rfl

/-- The permutation on machine numbers: `f` below `n`, the identity from `n` on. -/
def nat (i : Nat) : Nat := if h : i < n then (π.f ⟨i, h⟩).val else i

theorem nat_fin (x : Fin n) : π.nat x.val = (π.f x).val := by simp [nat, x.isLt]

theorem nat_g (x : Fin n) : π.nat (π.g x).val = x.val := by rw [nat_fin, π.fg]

theorem inv_nat_nat (i : Nat) : π⁻¹.nat (π.nat i) = i := by
  unfold nat
  by_cases h : i < n
  · simp only [h, ↓reduceDIte, (π.f ⟨i, h⟩).isLt, inv_f, π.gf]
  · simp [h]

theorem nat_inv_nat (i : Nat) : π.nat (π⁻¹.nat i) = i := (π⁻¹).inv_nat_nat i

theorem nat_inj {i j : Nat} (h : π.nat i = π.nat j) : i = j := by
  rw [← π.inv_nat_nat i, h, inv_nat_nat]

theorem nat_eq_iff {i j : Nat} : π.nat i = j ↔ i = π⁻¹.nat j := by
  constructor
  · intro h; rw [← h, inv_nat_nat]
  · intro h; rw [h, nat_inv_nat]

theorem f_inj {x y : Fin n} (h : π.f x = π.f y) : x = y := by rw [← π.gf x, h, π.gf]

theorem g_inj {x y : Fin n} (h : π.g x = π.g y) : x = y := by rw [← π.fg x, h, π.fg]

end MPerm

/-! ### Renaming the syntax -/

/-- The signature with machine `π.g m` at position `m`. -/
abbrev Sig.rename (S : Sig) (π : MPerm S.machines) : Sig :=
  { machines := S.machines, vars := fun m => S.vars (π.g m), states := fun m => S.states (π.g m) }

theorem Sig.rename_vars_len (S : Sig) (π : MPerm S.machines) (m : Fin S.machines) :
    (S.vars m).length = ((S.rename π).vars (π.f m)).length := by
  simp only [Sig.rename, π.gf]

/-- A reference of machine `π.g me`, as a reference of machine `me` of the renamed signature. -/
def Ref.rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} :
    Ref S (π.g me) → Ref (S.rename π) me
  | .own v => .own v
  | .other m v => .other (π.f m) (Fin.cast (S.rename_vars_len π m) v)
  | .state m => .state (π.f m)
  | .field f τ => .field f τ
  | .time => .time
  | .count g name => .count (g.map π.f) name
  | .agg op g => .agg op (g.map fun p => ⟨π.f p.1, Fin.cast (S.rename_vars_len π p.1) p.2⟩)
  | .absent τ => .absent τ

def Expr.rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} :
    Expr S (π.g me) → Expr (S.rename π) me
  | .val v => .val v
  | .ref r => .ref (r.rename π)
  | .un op a => .un op (a.rename π)
  | .bin op a b => .bin op (a.rename π) (b.rename π)

def renamePayload {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} :
    List (Nat × Expr S (π.g me)) → List (Nat × Expr (S.rename π) me)
  | [] => []
  | (f, x) :: rest => (f, x.rename π) :: renamePayload π rest

def Effect.rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} :
    Effect S (π.g me) → Effect (S.rename π) me
  | .set v rhs => .set v (rhs.rename π)
  | .emit ev after pl => .emit ev after (renamePayload π pl)
  | .timer n after ev pl => .timer n after ev (renamePayload π pl)
  | .cancel n => .cancel n
  | .reply ev after pl => .reply ev after (renamePayload π pl)

def Trans.rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} (t : Trans S (π.g me)) :
    Trans (S.rename π) me :=
  { src := t.src, dst := t.dst, event := t.event, guard := t.guard.rename π,
    effects := t.effects.map (Effect.rename π), faultOnly := t.faultOnly }

/-- The fault with the machines of the transitions it targets renamed. -/
def Fault.rename {n : Nat} (π : MPerm n) (f : Fault) : Fault :=
  { f with targets := f.targets.map (fun p => (π.nat p.1, p.2)) }

/-- The entry with its target and sender renamed. -/
def Entry.rename {n : Nat} (π : MPerm n) (e : Entry) : Entry :=
  { e with target := e.target.map π.nat, sender := e.sender.map π.nat }

def Label.rename {n : Nat} (π : MPerm n) (l : Label) : Label := { l with entry := l.entry.rename π }

/-- The machine list with machine `π.g j` at position `j`. -/
def permList {n : Nat} (π : MPerm n) (ms : List MState) : List MState :=
  List.ofFn (fun j : Fin n => ms.getD (π.g j).val ⟨0, []⟩)

/-- The configuration renamed (machines permuted, targets and senders renamed). -/
def Cfg.renameFull {n : Nat} (π : MPerm n) (c : Cfg) : Cfg :=
  { c with machines := permList π c.machines, pending := c.pending.map (Entry.rename π) }

/-- The configuration renamed when its machine list has length `n`, otherwise unchanged. -/
def Cfg.rename {n : Nat} (π : MPerm n) (c : Cfg) : Cfg :=
  if c.machines.length = n then c.renameFull π else c

def State.rename {n : Nat} (π : MPerm n) : State → State
  | .run m c => .run m (c.rename π)
  | .err m c => .err m (c.rename π)

/-- The system listed in the order `π`, whatever the length of its initial machine list. -/
@[reducible] def Sys.renameFull (sys : Sys) (π : MPerm sys.sig.machines) : Sys where
  sig := sys.sig.rename π
  trans m := (sys.trans (π.g m)).map (Trans.rename π)
  init := sys.init.renameFull π
  faults := sys.faults.map (Fault.rename π)
  stopAt := sys.stopAt
  samples := sys.samples.map (fun s => (π.nat s.1, s.2))

/-- **The system listed in the order `π`**: machine `π.g m'` of `sys` is machine `m'`, and every
reference to a machine is renamed. A system whose initial configuration does not have one machine
state per machine of its signature is left as it is. -/
def Sys.rename (sys : Sys) (π : MPerm sys.sig.machines) : Sys :=
  if sys.init.machines.length = sys.sig.machines then sys.renameFull π else sys

/-! ### The machine list -/

section
variable {n : Nat} (π : MPerm n)

@[simp] theorem permList_length (ms : List MState) : (permList π ms).length = n := by
  simp [permList]

theorem getElem?_permList {ms : List MState} (hl : ms.length = n) (j : Fin n) :
    (permList π ms)[j.val]? = ms[(π.g j).val]? := by
  have h1 : j.val < (permList π ms).length := by simp
  have h2 : (π.g j).val < ms.length := by rw [hl]; exact (π.g j).isLt
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
  simp [permList, List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem at?_permList {ms : List MState} (hl : ms.length = n) (m : Fin n) :
    at? (permList π ms) (π.f m).val = at? ms m.val := by
  unfold at?; rw [getElem?_permList π hl, π.gf]

theorem permList_set {ms : List MState} (hl : ms.length = n) (j : Fin n) (x : MState) :
    (permList π ms).set j.val x = permList π (ms.set (π.g j).val x) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · have hl' : (ms.set (π.g j).val x).length = n := by simp [hl]
    rw [show i = (⟨i, hi⟩ : Fin n).val from rfl, getElem?_permList π hl' ⟨i, hi⟩]
    by_cases hij : i = j.val
    · subst hij
      rw [List.getElem?_set_self (by simp : j.val < (permList π ms).length),
        show (⟨j.val, hi⟩ : Fin n) = j from rfl, List.getElem?_set_self (by rw [hl]; exact (π.g j).isLt)]
    · rw [List.getElem?_set_ne (Ne.symm hij), getElem?_permList π hl ⟨i, hi⟩,
        List.getElem?_set_ne]
      intro h
      apply hij
      have := congrArg Fin.val (π.g_inj (Fin.ext h))
      simp only at this
      omega
  · have h1 : (permList π ms).length ≤ i := by simp; omega
    have h2 : (permList π (ms.set (π.g j).val x)).length ≤ i := by simp; omega
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h2]

theorem permList_inv {ms : List MState} (hl : ms.length = n) : permList π⁻¹ (permList π ms) = ms := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [show i = (⟨i, hi⟩ : Fin n).val from rfl, getElem?_permList π⁻¹ (permList_length π ms) ⟨i, hi⟩,
      MPerm.inv_g, getElem?_permList π hl, π.gf]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

end

/-! ### Evaluation under a renaming -/

/-- The context with the snapshot permuted. -/
def Ctx.rename {n : Nat} (π : MPerm n) (cx : Ctx) : Ctx := { cx with snap := permList π cx.snap }

theorem countIn_rename {S : Sig} (π : MPerm S.machines) {snap : List MState}
    (hl : snap.length = S.machines) (name : String) :
    (g : List (Fin S.machines)) →
      countIn (S.rename π) (permList π snap) name (g.map π.f) = countIn S snap name g
  | [] => rfl
  | m :: g => by
    show countIn (S.rename π) (permList π snap) name (π.f m :: g.map π.f) = _
    unfold countIn
    rw [at?_permList π hl, countIn_rename π hl name g]
    simp only [Sig.rename, π.gf]

theorem intsIn_rename {S : Sig} (π : MPerm S.machines) {snap : List MState}
    (hl : snap.length = S.machines) :
    (g : List ((m : Fin S.machines) × Fin (S.vars m).length)) →
      intsIn (S := S.rename π) (permList π snap)
        (g.map fun p => ⟨π.f p.1, Fin.cast (S.rename_vars_len π p.1) p.2⟩) = intsIn snap g
  | [] => rfl
  | p :: g => by
    rw [List.map_cons]
    unfold intsIn
    rw [at?_permList π hl, intsIn_rename π hl g]
    rfl

theorem Ref.eval_rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} {cx : Ctx}
    (hl : cx.snap.length = S.machines) : (r : Ref S (π.g me)) →
    (r.rename π).eval (cx.rename π) = r.eval cx
  | .own v => rfl
  | .other m v => by
    simp only [Ref.rename, Ref.eval, Ctx.rename, at?_permList π hl, Fin.val_cast]
  | .state m => by
    simp only [Ref.rename, Ref.eval, Ctx.rename, at?_permList π hl]
    simp only [Sig.rename, π.gf]
  | .field f τ => rfl
  | .time => rfl
  | .count g name => by
    simp only [Ref.rename, Ref.eval, Ctx.rename, countIn_rename π hl]
  | .agg op g => by
    simp only [Ref.rename, Ref.eval, Ctx.rename, intsIn_rename π hl]
  | .absent τ => rfl

theorem Expr.eval_rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} {cx : Ctx}
    (hl : cx.snap.length = S.machines) : (x : Expr S (π.g me)) →
    (x.rename π).eval (cx.rename π) = x.eval cx
  | .val v => rfl
  | .ref r => by simp only [Expr.rename, Expr.eval, Ref.eval_rename π hl r]
  | .un op a => by simp only [Expr.rename, Expr.eval, Expr.eval_rename π hl a]
  | .bin op a b => by
    have ha := Expr.eval_rename π hl a
    have hb := Expr.eval_rename π hl b
    cases op <;> simp only [Expr.rename, Expr.eval, ha, hb]

/-! ### Effects, firing and phase 2 under a renaming -/

/-- A map on the success value of a step result. -/
def rmap {α β : Type} (f : α → β) : Except Err α → Except Err β
  | .ok a => .ok (f a)
  | .error e => .error e

@[simp] theorem rmap_ok {α β : Type} (f : α → β) (a : α) : rmap f (.ok a) = .ok (f a) := rfl
@[simp] theorem rmap_error {α β : Type} (f : α → β) (e : Err) : rmap f (.error e : Except Err α) = .error e := rfl

/-- What a winner produced, renamed. -/
def Out.rename {n : Nat} (π : MPerm n) (o : Out) : Out := (o.1.map (Entry.rename π), o.2)

theorem ctxOf_renameFull {n : Nat} (π : MPerm n) (c : Cfg) (e : Entry) (own : MState) :
    ctxOf (c.renameFull π) (e.rename π) own = (ctxOf c e own).rename π := rfl

theorem evalPayload_rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} {cx : Ctx}
    (hl : cx.snap.length = S.machines) : (pl : List (Nat × Expr S (π.g me))) →
    evalPayload (cx.rename π) (renamePayload π pl) = evalPayload cx pl
  | [] => rfl
  | (f, x) :: rest => by
    unfold renamePayload evalPayload
    rw [Expr.eval_rename π hl x, evalPayload_rename π hl rest]

theorem runEffects_rename {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} {c : Cfg} (e : Entry)
    (hl : c.machines.length = S.machines) :
    (effs : List (Effect S (π.g me))) → (own : MState) →
    runEffects (c.renameFull π) (e.rename π) (effs.map (Effect.rename π)) own =
      rmap (fun r => (r.1, Out.rename π r.2)) (runEffects c e effs own)
  | [], own => rfl
  | .set v rhs :: rest, own => by
    rw [List.map_cons]
    unfold Effect.rename runEffects
    rw [ctxOf_renameFull, Expr.eval_rename π hl]
    cases rhs.eval (ctxOf c e own) with
    | error err => rfl
    | ok x =>
      dsimp only
      cases Val.check ((S.vars (π.g me)).get v) x with
      | error err => rfl
      | ok x' =>
        dsimp only
        split
        · exact runEffects_rename π e hl rest _
        · rfl
  | .emit ev after pl :: rest, own => by
    rw [List.map_cons]
    unfold Effect.rename runEffects
    rw [ctxOf_renameFull, evalPayload_rename π hl]
    show (if timeLimit ≤ c.time + after then _ else _) = rmap _ (if timeLimit ≤ c.time + after then _ else _)
    split
    · rfl
    · cases evalPayload (ctxOf c e own) pl with
      | error err => rfl
      | ok vs =>
        dsimp only
        erw [runEffects_rename π e hl rest own]
        cases runEffects c e rest own with
        | error err => rfl
        | ok r =>
          obtain ⟨st, outs, tn⟩ := r
          simp [Out.rename, Entry.rename, π.nat_g, Cfg.renameFull]
  | .timer k after ev pl :: rest, own => by
    rw [List.map_cons]
    unfold Effect.rename runEffects
    rw [ctxOf_renameFull, evalPayload_rename π hl]
    show (if timeLimit ≤ c.time + after then _ else _) = rmap _ (if timeLimit ≤ c.time + after then _ else _)
    split
    · rfl
    · cases evalPayload (ctxOf c e own) pl with
      | error err => rfl
      | ok vs =>
        dsimp only
        erw [runEffects_rename π e hl rest own]
        cases runEffects c e rest own with
        | error err => rfl
        | ok r =>
          obtain ⟨st, outs, tn⟩ := r
          by_cases hk : k ∈ tn <;> simp [Out.rename, Entry.rename, π.nat_g, Cfg.renameFull, hk]
  | .cancel k :: rest, own => by
    rw [List.map_cons]
    unfold Effect.rename runEffects
    erw [runEffects_rename π e hl rest own]
    cases runEffects c e rest own with
    | error err => rfl
    | ok r => rfl
  | .reply ev after pl :: rest, own => by
    rw [List.map_cons]
    unfold Effect.rename runEffects
    rw [ctxOf_renameFull, evalPayload_rename π hl]
    show (if timeLimit ≤ c.time + after then _ else _) = rmap _ (if timeLimit ≤ c.time + after then _ else _)
    split
    · rfl
    · cases evalPayload (ctxOf c e own) pl with
      | error err => rfl
      | ok vs =>
        dsimp only
        cases hs : e.sender with
        | none => simp [Entry.rename, hs]
        | some to =>
          have hs' : (e.rename π).sender = some (π.nat to) := by simp [Entry.rename, hs]
          rw [hs']
          dsimp only
          erw [runEffects_rename π e hl rest own]
          cases runEffects c e rest own with
          | error err => rfl
          | ok r =>
            obtain ⟨st, outs, tn⟩ := r
            simp [Out.rename, Entry.rename, π.nat_g, Cfg.renameFull]

/-! ### Winners and phase 2 under a renaming -/

section
variable {sys : Sys} (π : MPerm sys.sig.machines)

/-- A winner of the renamed system, as the winner of `sys` it renames. -/
def Winner.back (w : Winner (sys.renameFull π)) : Winner sys :=
  ⟨π.g w.mach, Fin.cast (List.length_map _) w.idx⟩

theorem trans_get_renameFull (m : Fin sys.sig.machines) (i : Fin ((sys.renameFull π).trans m).length) :
    ((sys.renameFull π).trans m).get i =
      Trans.rename π ((sys.trans (π.g m)).get (Fin.cast (List.length_map _) i)) := by
  simp only [List.get_eq_getElem, List.getElem_map]; rfl

/-- The emitted blocks renamed. -/
def Emitted.rename {n : Nat} (π' : MPerm n) (bs : Emitted) : Emitted :=
  bs.map (fun b => (π'.nat b.1, Out.rename π' b.2))

theorem fireOne_rename {c : Cfg} (e : Entry) (hl : c.machines.length = sys.sig.machines)
    (w : Winner (sys.renameFull π)) (own : MState) :
    fireOne (sys.renameFull π) (c.renameFull π) (e.rename π) w own =
      rmap (fun r => (r.1, Out.rename π r.2)) (fireOne sys c e (Winner.back π w) own) := by
  unfold fireOne
  dsimp only
  rw [trans_get_renameFull]
  simp only [Trans.rename]
  rw [runEffects_rename π e hl]
  simp only [Winner.back]
  cases runEffects c e ((sys.trans (π.g w.mach)).get (Fin.cast (List.length_map _) w.idx)).effects own with
  | error err => rfl
  | ok r => rfl

theorem phase2_rename {c : Cfg} (e : Entry) (hl : c.machines.length = sys.sig.machines) :
    (ws : List (Winner (sys.renameFull π))) → (ms : List MState) → ms.length = sys.sig.machines →
    phase2 (sys.renameFull π) (c.renameFull π) (e.rename π) ws (permList π ms) =
      rmap (fun r => (permList π r.1, Emitted.rename π r.2)) (phase2 sys c e (ws.map (Winner.back π)) ms)
  | [], ms, _ => rfl
  | w :: ws, ms, hm => by
    simp only [List.map_cons]
    unfold phase2
    have hget : (permList π ms)[w.mach.val]? = ms[(Winner.back π w).mach.val]? :=
      getElem?_permList π hm w.mach
    rw [hget]
    cases ms[(Winner.back π w).mach.val]? with
    | none => rfl
    | some own =>
      dsimp only
      rw [fireOne_rename π e hl]
      cases fireOne sys c e (Winner.back π w) own with
      | error err => rfl
      | ok r =>
        obtain ⟨st, out⟩ := r
        dsimp only [rmap]
        have hset : (permList π ms).set w.mach.val st = permList π (ms.set (π.g w.mach).val st) :=
          permList_set π hm w.mach st
        rw [hset, phase2_rename e hl ws _ (by simp [hm])]
        simp only [Winner.back]
        cases phase2 sys c e (ws.map (Winner.back π)) (ms.set (π.g w.mach).val st) with
        | error err => rfl
        | ok r' =>
          simp [Emitted.rename]
          try exact (π.nat_g w.mach).symm

end

/-! ### Faults under a renaming -/

theorem targets?_rename {n : Nat} (π : MPerm n) (f : Fault) (k : FKind) (m i t : Nat) :
    (f.rename π).targets? k m i t = f.targets? k (π⁻¹.nat m) i t := by
  simp only [Fault.targets?, Fault.rename, Fault.actsAt]
  congr 2
  apply decide_eq_decide.mpr
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, b⟩, hm, h1, rfl⟩
    rw [← h1, π.inv_nat_nat]; exact hm
  · intro hm
    exact ⟨(π⁻¹.nat m, i), hm, π.nat_inv_nat m, rfl⟩

theorem hits_rename {n : Nat} (π : MPerm n) (f : Fault) (ks : List FKind) (ev att t : Nat) :
    (f.rename π).hits ks ev att t = f.hits ks ev att t := rfl

/-- The active faults renamed. -/
def renameAct {n : Nat} (π : MPerm n) (act : List (Nat × Fault)) : List (Nat × Fault) :=
  act.map (fun p => (p.1, p.2.rename π))

theorem zip_filter_rename {n : Nat} (π : MPerm n) (mask : List Bool) :
    (r : List Nat) → (fs : List Fault) →
    (r.zip (fs.map (Fault.rename π))).filter (fun p => mask.getD p.1 false) =
      renameAct π ((r.zip fs).filter (fun p => mask.getD p.1 false))
  | r, fs => by
    simp only [renameAct, List.zip_map_right, List.filter_map]; rfl

theorem active_renameFull (sys : Sys) (π : MPerm sys.sig.machines) (mask : List Bool) :
    (sys.renameFull π).active mask = renameAct π (sys.active mask) := by
  simp only [Sys.active, Sys.renameFull, List.length_map]
  exact zip_filter_rename π mask _ _

section
variable {sys : Sys} (π : MPerm sys.sig.machines)

theorem finList_cast {a b : Nat} (h : a = b) : (finList a).map (Fin.cast h) = finList b := by
  subst h; simp

theorem scan_rename {act : List (Nat × Fault)} {c : Cfg} (e : Entry)
    (hl : c.machines.length = sys.sig.machines) (m : Fin sys.sig.machines) (own : MState) :
    (is : List (Fin ((sys.renameFull π).trans m).length)) →
    rmap (Option.map (Fin.cast (List.length_map _)))
        (scan (sys.renameFull π) (renameAct π act) (c.renameFull π) (e.rename π) m own is) =
      scan sys act c e (π.g m) own (is.map (Fin.cast (List.length_map _)))
  | [] => rfl
  | i :: is => by
    have ih := scan_rename (act := act) e hl m own is
    simp only [List.map_cons]
    unfold scan
    rw [trans_get_renameFull]
    simp only [Trans.rename, renameAct, List.any_map, Function.comp_def, targets?_rename]
    have hm : π⁻¹.nat m.val = (π.g m).val := by
      rw [MPerm.nat_fin]; rfl
    simp only [hm, Fin.val_cast]
    have hev : (e.rename π).event = e.event := rfl
    have ht : (e.rename π).time = e.time := rfl
    rw [hev, ht]
    split
    · split
      · exact ih
      · rw [ctxOf_renameFull, Expr.eval_rename π hl]
        split
        · split
          · exact ih
          · rfl
        · exact ih
        · rfl
        · rfl
    · exact ih

theorem choose_rename {act : List (Nat × Fault)} {c : Cfg} (e : Entry)
    (hl : c.machines.length = sys.sig.machines) (m : Fin sys.sig.machines) :
    rmap (Option.map (Winner.back π))
        (choose (sys.renameFull π) (renameAct π act) (c.renameFull π) (e.rename π) m) =
      choose sys act c e (π.g m) := by
  unfold choose
  have hat : at? (c.renameFull π).machines m.val = at? c.machines (π.g m).val := by
    have := at?_permList π hl (π.g m)
    rw [π.fg] at this
    exact this
  rw [hat]
  cases at? c.machines (π.g m).val with
  | error err => rfl
  | ok own =>
    dsimp only
    have hs := scan_rename π e hl (act := act) m own (finList ((sys.renameFull π).trans m).length)
    erw [finList_cast] at hs
    rw [← hs]
    cases scan (sys.renameFull π) (renameAct π act) (c.renameFull π) (e.rename π) m own
        (finList ((sys.renameFull π).trans m).length) with
    | error err => rfl
    | ok o => cases o <;> rfl

theorem winnersOf_rename {act : List (Nat × Fault)} {c : Cfg} (e : Entry)
    (hl : c.machines.length = sys.sig.machines) : (L : List (Fin sys.sig.machines)) →
    rmap (List.map (Winner.back π))
        (winnersOf (sys.renameFull π) (renameAct π act) (c.renameFull π) (e.rename π) L) =
      winnersOf sys act c e (L.map π.g)
  | [] => rfl
  | m :: L => by
    simp only [List.map_cons]
    unfold winnersOf
    rw [← choose_rename π e hl m, ← winnersOf_rename e hl L]
    cases choose (sys.renameFull π) (renameAct π act) (c.renameFull π) (e.rename π) m with
    | error err => rfl
    | ok o =>
      cases winnersOf (sys.renameFull π) (renameAct π act) (c.renameFull π) (e.rename π) L with
      | error err => rfl
      | ok ws => cases o <;> rfl

end

/-! ### Winners over a permuted list of machines -/

/-- The winner `choose` gives a machine, if it succeeds. -/
def chooseOpt (sys : Sys) (act : List (Nat × Fault)) (c : Cfg) (e : Entry) (m : Fin sys.sig.machines) :
    Option (Winner sys) :=
  match choose sys act c e m with
  | .ok o => o
  | .error _ => none

theorem winnersOf_ok_iff {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry} :
    (L : List (Fin sys.sig.machines)) → (ws : List (Winner sys)) →
    (winnersOf sys act c e L = .ok ws ↔
      (∀ m ∈ L, ∃ o, choose sys act c e m = .ok o) ∧ ws = L.filterMap (chooseOpt sys act c e))
  | [], ws => by simp [winnersOf, eq_comm]
  | m :: L, ws => by
    unfold winnersOf
    cases hc : choose sys act c e m with
    | error err => simp [hc]
    | ok o =>
      cases hw : winnersOf sys act c e L with
      | error err =>
        constructor
        · intro h; cases h
        · rintro ⟨hall, -⟩
          have := (winnersOf_ok_iff L (L.filterMap (chooseOpt sys act c e))).mpr
            ⟨fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'), rfl⟩
          rw [hw] at this; cases this
      | ok ws' =>
        have ih := (winnersOf_ok_iff L ws').mp hw
        constructor
        · intro h
          cases h
          refine ⟨?_, ?_⟩
          · intro m' hm'
            rcases List.mem_cons.mp hm' with rfl | hm'
            · exact ⟨o, hc⟩
            · exact ih.1 m' hm'
          · rw [List.filterMap_cons, ← ih.2]; simp only [chooseOpt, hc]; cases o <;> rfl
        · rintro ⟨-, rfl⟩
          rw [List.filterMap_cons, ← ih.2]; simp only [chooseOpt, hc]; cases o <;> rfl

theorem winnersOf_perm {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    {L L' : List (Fin sys.sig.machines)} (hp : L.Perm L') {ws : List (Winner sys)}
    (h : winnersOf sys act c e L = .ok ws) : ∃ ws', winnersOf sys act c e L' = .ok ws' ∧ ws.Perm ws' := by
  obtain ⟨hall, rfl⟩ := (winnersOf_ok_iff L ws).mp h
  refine ⟨L'.filterMap (chooseOpt sys act c e), (winnersOf_ok_iff L' _).mpr
    ⟨fun m hm => hall m (hp.mem_iff.mpr hm), rfl⟩, hp.filterMap _⟩

theorem winnersOf_perm_err {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    {L L' : List (Fin sys.sig.machines)} (hp : L.Perm L') {err : Err}
    (h : winnersOf sys act c e L = .error err) : ∃ err', winnersOf sys act c e L' = .error err' := by
  cases h' : winnersOf sys act c e L' with
  | error err' => exact ⟨err', rfl⟩
  | ok ws' =>
    obtain ⟨ws, hws, -⟩ := winnersOf_perm hp.symm h'
    rw [h] at hws; cases hws

theorem addressed_rename {n : Nat} (π : MPerm n) (e : Entry) :
    ((addressed n (e.rename π)).map π.g).Perm (addressed n e) := by
  have hnd1 : ((addressed n (e.rename π)).map π.g).Nodup := by
    exact List.Pairwise.map π.g (fun a b h hab => h (π.g_inj hab))
      ((finList_nodup n).sublist List.filter_sublist)
  have hnd2 : (addressed n e).Nodup := (finList_nodup n).sublist List.filter_sublist
  apply (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr
  intro m
  simp only [List.mem_map, addressed, List.mem_filter, Entry.rename]
  constructor
  · rintro ⟨m', ⟨-, hm'⟩, rfl⟩
    refine ⟨mem_finList n _, ?_⟩
    cases ht : e.target with
    | none => rfl
    | some t =>
      rw [ht] at hm'
      simp only [Option.map_some, Option.all_some, beq_iff_eq] at hm' ⊢
      rw [π.nat_eq_iff] at hm'
      rw [hm', MPerm.nat_fin]; rfl
  · intro ⟨_, hm⟩
    refine ⟨π.f m, ⟨mem_finList n _, ?_⟩, π.gf m⟩
    cases ht : e.target with
    | none => rfl
    | some t =>
      rw [ht] at hm
      simp only [Option.map_some, Option.all_some, beq_iff_eq] at hm ⊢
      rw [hm, MPerm.nat_fin]

/-! ### Entries, the queue and the configuration under a renaming -/

section
variable {n : Nat} (π : MPerm n)

theorem Entry.rename_inj {a b : Entry} (h : a.rename π = b.rename π) : a = b := by
  obtain ⟨t1, e1, p1, g1, m1, d1, s1⟩ := a
  obtain ⟨t2, e2, p2, g2, m2, d2, s2⟩ := b
  simp only [Entry.rename, Entry.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, hg, rfl, rfl, hs⟩ := h
  have hinj : ∀ (x y : Option Nat), x.map π.nat = y.map π.nat → x = y := by
    intro x y hxy
    cases x <;> cases y <;> simp at hxy ⊢
    exact π.nat_inj hxy
  rw [hinj _ _ hg, hinj _ _ hs]

@[simp] theorem Entry.rename_time (e : Entry) : (e.rename π).time = e.time := rfl
@[simp] theorem Entry.rename_event (e : Entry) : (e.rename π).event = e.event := rfl
@[simp] theorem Entry.rename_done (e : Entry) : (e.rename π).done = e.done := rfl

theorem erase_map_rename (a : Entry) : (l : List Entry) →
    (l.map (Entry.rename π)).erase (a.rename π) = (l.erase a).map (Entry.rename π)
  | [] => rfl
  | b :: l => by
    simp only [List.map_cons, List.erase_cons]
    by_cases h : b = a
    · subst h; simp
    · have h' : ¬ (b.rename π = a.rename π) := fun h' => h (Entry.rename_inj π h')
      simp [h, h', erase_map_rename a l]

theorem insertByTime_rename (x : Entry) : (q : List Entry) →
    insertByTime (q.map (Entry.rename π)) (x.rename π) = (insertByTime q x).map (Entry.rename π)
  | [] => rfl
  | y :: q => by
    simp only [List.map_cons, insertByTime, Entry.rename_time]
    by_cases h : x.time < y.time
    · simp [h]
    · simp [h, insertByTime_rename x q]

theorem foldl_insertByTime_rename : (l q : List Entry) →
    (l.map (Entry.rename π)).foldl insertByTime (q.map (Entry.rename π)) =
      (l.foldl insertByTime q).map (Entry.rename π)
  | [], q => rfl
  | x :: l, q => by
    simp only [List.map_cons, List.foldl_cons, insertByTime_rename]
    exact foldl_insertByTime_rename l _

theorem Cfg.popE_renameFull (c : Cfg) (e : Entry) :
    (c.popE e).renameFull π = (c.renameFull π).popE (e.rename π) := by
  simp only [Cfg.popE, Cfg.renameFull, Cfg.attemptsOf, erase_map_rename, Entry.rename_event,
    Entry.rename_time]

theorem Cfg.enq_renameFull (c : Cfg) (x : Entry) :
    (c.enq x).renameFull π = (c.renameFull π).enq (x.rename π) := by
  simp only [Cfg.enq, Cfg.renameFull, insertByTime_rename]

@[simp] theorem Cfg.renameFull_attemptsOf (c : Cfg) (ev : Nat) :
    (c.renameFull π).attemptsOf ev = c.attemptsOf ev := rfl

@[simp] theorem Cfg.renameFull_machines_length (c : Cfg) :
    (c.renameFull π).machines.length = n := by simp [Cfg.renameFull]

theorem mem_map_rename {e : Entry} {l : List Entry} :
    e.rename π ∈ l.map (Entry.rename π) ↔ e ∈ l := by
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    rw [← Entry.rename_inj π he]; exact hx
  · exact List.mem_map_of_mem

theorem later_rename (e : Entry) (i b : Nat) :
    later (e.rename π) i b = rmap (Entry.rename π) (later e i b) := by
  unfold later
  by_cases h : timeLimit ≤ e.time + b <;> simp [h, rmap, Entry.rename]

theorem delayFault_rename (act : List (Nat × Fault)) (e : Entry) (att : Nat) :
    delayFault (renameAct π act) (e.rename π) att = (delayFault act e att).map (fun p => (p.1, p.2.rename π)) := by
  simp only [delayFault, renameAct, List.find?_map]; rfl

theorem dupFault_rename (act : List (Nat × Fault)) (e : Entry) (att : Nat) :
    dupFault (renameAct π act) (e.rename π) att = (dupFault act e att).map (fun p => (p.1, p.2.rename π)) := by
  simp only [dupFault, renameAct, List.find?_map]; rfl

theorem dropHit_rename (act : List (Nat × Fault)) (e : Entry) (att : Nat) :
    dropHit (renameAct π act) (e.rename π) att ↔ dropHit act e att := by
  simp only [dropHit, renameAct, List.any_map]; rfl

/-! ### The commit -/

theorem foldl_insertByTime_perm_append : (l q : List Entry) → (l.foldl insertByTime q).Perm (q ++ l)
  | [], q => by simp
  | x :: l, q => by
    simp only [List.foldl_cons]
    refine (foldl_insertByTime_perm_append l _).trans ?_
    refine ((insertByTime_perm q x).append (List.Perm.refl l)).trans ?_
    exact (List.perm_middle).symm

theorem foldl_insertByTime_perm2 {l l' q q' : List Entry} (hl : l.Perm l') (hq : q.Perm q') :
    (l.foldl insertByTime q).Perm (l'.foldl insertByTime q') :=
  (foldl_insertByTime_perm_append l q).trans ((hq.append hl).trans (foldl_insertByTime_perm_append l' q').symm)

theorem blockOf_rename (m : Nat) : (bs : Emitted) →
    blockOf m (Emitted.rename π bs) = (blockOf (π⁻¹.nat m) bs).map (Entry.rename π)
  | [] => rfl
  | (i, out) :: bs => by
    simp only [Emitted.rename, List.map_cons, blockOf]
    have hiff : (π.nat i = m) ↔ (i = π⁻¹.nat m) := π.nat_eq_iff
    by_cases h : i = π⁻¹.nat m
    · rw [if_pos (hiff.mpr h), if_pos h]; rfl
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
      exact blockOf_rename m bs

theorem range_map_inv_perm : ((List.range n).map π⁻¹.nat).Perm (List.range n) := by
  have hnd : ((List.range n).map π⁻¹.nat).Nodup :=
    List.Pairwise.map _ (fun a b h hab => h ((π⁻¹).nat_inj hab)) List.nodup_range
  apply (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr
  intro x
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MPerm.nat, hy, ↓reduceDIte]
    exact (π⁻¹.f ⟨y, hy⟩).isLt
  · intro hx
    refine ⟨π.nat x, ?_, π.inv_nat_nat x⟩
    simp only [MPerm.nat, hx, ↓reduceDIte]
    exact (π.f ⟨x, hx⟩).isLt

theorem inMachineOrder_rename (bs : Emitted) :
    (inMachineOrder n (Emitted.rename π bs)).Perm ((inMachineOrder n bs).map (Entry.rename π)) := by
  simp only [inMachineOrder, blockOf_rename, List.map_flatMap]
  rw [← List.flatMap_map π⁻¹.nat (fun m => (blockOf m bs).map (Entry.rename π))]
  exact (range_map_inv_perm π).flatMap_right _

theorem touchedOf_rename (bs : Emitted) :
    touchedOf (Emitted.rename π bs) = (touchedOf bs).map (fun p => (π.nat p.1, p.2)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [Emitted.rename, List.map_cons, touchedOf, List.flatMap_cons, List.map_append,
      List.map_map] at ih ⊢
    rw [ih]; rfl

theorem isTimerOf_rename (bs : Emitted) (x : Entry) :
    isTimerOf (touchedOf (Emitted.rename π bs)) (x.rename π) = isTimerOf (touchedOf bs) x := by
  rw [touchedOf_rename]
  simp only [isTimerOf, Entry.rename]
  cases x.target with
  | none => rfl
  | some m =>
    cases x.timer with
    | none => rfl
    | some k =>
      simp only [Option.map_some]
      apply decide_eq_decide.mpr
      simp only [List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨a, b⟩, hm, h1, rfl⟩
        rw [← π.nat_inj h1]; exact hm
      · intro hm; exact ⟨(m, k), hm, rfl, rfl⟩

theorem commit_rename (c0 : Cfg) (ms : List MState) (bs : Emitted) :
    ((c0.renameFull π).commit n (permList π ms) (Emitted.rename π bs)).Approx
      ((c0.commit n ms bs).renameFull π) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [Cfg.commit, Cfg.renameFull]
  have hf : (c0.pending.map (Entry.rename π)).filter (fun x => !isTimerOf (touchedOf (Emitted.rename π bs)) x) =
      (c0.pending.filter (fun x => !isTimerOf (touchedOf bs) x)).map (Entry.rename π) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x _
    simp only [Function.comp_def, isTimerOf_rename]
  rw [hf, ← foldl_insertByTime_rename]
  exact foldl_insertByTime_perm2 (inMachineOrder_rename π bs) (List.Perm.refl _)

theorem Dup.rename {act : List (Nat × Fault)} {e : Entry} {att : Nat} {c1 c1' c2 : Cfg}
    (h : c1'.Approx (c1.renameFull π)) (hd : Dup act e att c1 c2) :
    ∃ c2', Dup (renameAct π act) (e.rename π) att c1' c2' ∧ c2'.Approx (c2.renameFull π) := by
  cases hd with
  | none h0 =>
    exact ⟨c1', Dup.none (by rw [dupFault_rename, h0]; rfl), h⟩
  | some h0 hl =>
    refine ⟨c1'.enq _, Dup.some (by rw [dupFault_rename, h0]; rfl)
      (by simp only [Fault.rename, later_rename, hl]; rfl), ?_⟩
    rw [Cfg.enq_renameFull]
    exact Cfg.enq_approx h _

theorem Dup.unrename {act : List (Nat × Fault)} {e : Entry} {att : Nat} {c1 c1' c2' : Cfg}
    (h : c1'.Approx (c1.renameFull π)) (hd : Dup (renameAct π act) (e.rename π) att c1' c2') :
    ∃ c2, Dup act e att c1 c2 ∧ c2'.Approx (c2.renameFull π) := by
  cases hd with
  | none h0 =>
    refine ⟨c1, Dup.none ?_, h⟩
    rw [dupFault_rename] at h0
    cases h1 : dupFault act e att with
    | none => rfl
    | some p => rw [h1] at h0; cases h0
  | some h0 hl =>
    rename_i i f cp
    rw [dupFault_rename] at h0
    cases h1 : dupFault act e att with
    | none => rw [h1] at h0; cases h0
    | some p =>
      obtain ⟨i0, f0⟩ := p
      rw [h1] at h0
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      simp only [Fault.rename] at hl
      rw [later_rename] at hl
      cases h2 : later e i0 f0.by_ with
      | error err => rw [h2] at hl; cases hl
      | ok cp0 =>
        rw [h2] at hl
        cases hl
        refine ⟨c1.enq cp0, Dup.some h1 h2, ?_⟩
        rw [Cfg.enq_renameFull]
        exact Cfg.enq_approx h _

end

/-! ### Draws under a renaming -/

theorem rmap_eq_ok {α β : Type} {f : α → β} {x : Except Err α} {y : β} (h : rmap f x = .ok y) :
    ∃ a, x = .ok a ∧ f a = y := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

theorem rmap_eq_error {α β : Type} {f : α → β} {x : Except Err α} {e : Err} (h : rmap f x = .error e) :
    x = .error e := by
  cases x with
  | error e' => cases h; rfl
  | ok a => cases h

theorem Effect.rename_withAfter {S : Sig} (π : MPerm S.machines) {me : Fin S.machines} (a : Nat)
    (eff : Effect S (π.g me)) : (eff.withAfter a).rename π = (eff.rename π).withAfter a := by
  cases eff <;> rfl

theorem siteDraw_renameFull (sys : Sys) (π : MPerm sys.sig.machines) (ds : List Nat)
    (m : Fin sys.sig.machines) (i j : Nat) :
    (sys.renameFull π).siteDraw ds m.val i j = sys.siteDraw ds (π.g m).val i j := by
  simp only [Sys.siteDraw, Sys.renameFull, List.findIdx?_map]
  congr 2
  funext s
  simp only [Function.comp_def]
  congr 1
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, π.nat_eq_iff]
  have : π⁻¹.nat m.val = (π.g m).val := by rw [MPerm.nat_fin]; rfl
  rw [this]

theorem resolve_renameFull (sys : Sys) (π : MPerm sys.sig.machines) (ds : List Nat) :
    (sys.renameFull π).resolve ds = (sys.resolve ds).renameFull π := by
  simp only [Sys.resolve]
  congr 1
  funext m
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_mapIdx, List.getElem_map, Trans.rename]
    congr 1
    apply List.ext_getElem
    · simp
    · intro j k1 k2
      simp only [List.getElem_mapIdx, List.getElem_map]
      rw [siteDraw_renameFull]
      split <;> simp [Effect.rename_withAfter]

theorem dists_renameFull (sys : Sys) (π : MPerm sys.sig.machines) :
    (sys.renameFull π).dists = sys.dists := by
  simp [Sys.dists, Sys.renameFull, List.map_map, Function.comp_def]

/-! ### Winners of the renamed system -/

section
variable {R : Sys} (π : MPerm R.sig.machines)

theorem winners_rename_fwd {act : List (Nat × Fault)} {c0 : Cfg} {e : Entry} {ws : List (Winner R)}
    (hl : c0.machines.length = R.sig.machines) (h : winners R act c0 e = .ok ws) :
    ∃ ws', winners (R.renameFull π) (renameAct π act) (c0.renameFull π) (e.rename π) = .ok ws' ∧
      (ws'.map (Winner.back π)).Perm ws := by
  obtain ⟨ws2, h2, hp⟩ := winnersOf_perm (addressed_rename π e).symm h
  have hr := winnersOf_rename π e hl (act := act) (addressed R.sig.machines (e.rename π))
  rw [h2] at hr
  obtain ⟨ws', hws', rfl⟩ := rmap_eq_ok hr
  exact ⟨ws', hws', hp.symm⟩

theorem winners_rename_bwd {act : List (Nat × Fault)} {c0 : Cfg} {e : Entry}
    {ws' : List (Winner (R.renameFull π))} (hl : c0.machines.length = R.sig.machines)
    (h : winners (R.renameFull π) (renameAct π act) (c0.renameFull π) (e.rename π) = .ok ws') :
    ∃ ws, winners R act c0 e = .ok ws ∧ (ws'.map (Winner.back π)).Perm ws := by
  have hr := winnersOf_rename π e hl (act := act) (addressed R.sig.machines (e.rename π))
  have h' : winnersOf (R.renameFull π) (renameAct π act) (c0.renameFull π) (e.rename π)
      (addressed R.sig.machines (e.rename π)) = .ok ws' := h
  rw [h'] at hr
  obtain ⟨ws, hws, hp⟩ := winnersOf_perm (addressed_rename π e) hr.symm
  exact ⟨ws, hws, hp⟩

theorem winners_rename_err {act : List (Nat × Fault)} {c0 : Cfg} {e : Entry}
    (hl : c0.machines.length = R.sig.machines) :
    (∃ err, winners (R.renameFull π) (renameAct π act) (c0.renameFull π) (e.rename π) = .error err) ↔
      ∃ err, winners R act c0 e = .error err := by
  have hr := winnersOf_rename π e hl (act := act) (addressed R.sig.machines (e.rename π))
  constructor
  · rintro ⟨err, h⟩
    have h' : winnersOf (R.renameFull π) (renameAct π act) (c0.renameFull π) (e.rename π)
        (addressed R.sig.machines (e.rename π)) = .error err := h
    rw [h'] at hr
    exact winnersOf_perm_err (addressed_rename π e) hr.symm
  · rintro ⟨err, h⟩
    obtain ⟨err', h2⟩ := winnersOf_perm_err (addressed_rename π e).symm h
    rw [h2] at hr
    cases hx : winnersOf (R.renameFull π) (renameAct π act) (c0.renameFull π) (e.rename π)
        (addressed R.sig.machines (e.rename π)) with
    | error err'' => exact ⟨err'', hx⟩
    | ok ws => rw [hx] at hr; cases hr

end

/-! ### Phase 2 over permuted winners -/

theorem phase2_perm_ok {R : Sys} {c0 : Cfg} {e : Entry} {ws ws2 : List (Winner R)} (hp : ws.Perm ws2)
    (hnd : (ws.map (·.mach)).Nodup) {r : List MState × Emitted}
    (h : phase2 R c0 e ws c0.machines = .ok r) :
    ∃ r2, phase2 R c0 e ws2 c0.machines = .ok r2 ∧
      c0.commit R.sig.machines r2.1 r2.2 = c0.commit R.sig.machines r.1 r.2 := by
  have ha := afterPhase2_perm (c0 := c0) (e := e) hp hnd
  rw [h] at ha
  cases h2 : phase2 R c0 e ws2 c0.machines with
  | error err => rw [h2] at ha; simp [afterPhase2, Except.toOption] at ha
  | ok r2 =>
    rw [h2] at ha
    simp only [afterPhase2, Except.toOption, Option.some.injEq] at ha
    exact ⟨r2, rfl, ha⟩

theorem phase2_perm_err {R : Sys} {c0 : Cfg} {e : Entry} {ws ws2 : List (Winner R)} (hp : ws.Perm ws2)
    (hnd : (ws.map (·.mach)).Nodup) {err : Err} (h : phase2 R c0 e ws c0.machines = .error err) :
    ∃ err', phase2 R c0 e ws2 c0.machines = .error err' := by
  cases h2 : phase2 R c0 e ws2 c0.machines with
  | error err' => exact ⟨err', rfl⟩
  | ok r2 =>
    have hnd2 : (ws2.map (·.mach)).Nodup := hnd.perm (hp.map _)
    obtain ⟨r, hr, -⟩ := phase2_perm_ok hp.symm hnd2 h2
    rw [h] at hr; cases hr

theorem winners_nodup_back {R : Sys} (π : MPerm R.sig.machines) {act : List (Nat × Fault)} {c0 : Cfg}
    {e : Entry} {ws : List (Winner R)} {ws' : List (Winner (R.renameFull π))}
    (h : winners R act c0 e = .ok ws) (hp : (ws'.map (Winner.back π)).Perm ws) :
    ((ws'.map (Winner.back π)).map (·.mach)).Nodup :=
  (winners_nodup h).perm (hp.map _).symm

/-! ### A step of the renamed system -/

/-- The state renamed (whatever the length of its machine list). -/
def State.renameFull {n : Nat} (π : MPerm n) : State → State
  | .run m c => .run m (c.renameFull π)
  | .err m c => .err m (c.renameFull π)

/-- `Step.deliverOk` with the system of the draws named. -/
theorem Step.deliverOk_via {sys : Sys} {mask : List Bool} {c : Cfg} {l : Label} {X : Sys}
    (hX : sys.resolve l.draws = X) {ws : List (Winner X)} {ms : List MState} {bs : Emitted} {c'' : Cfg}
    (hd : DrawsOk sys l.draws) (hr : Ready sys c l.entry)
    (hdr : ¬ dropHit (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1))
    (hn : delayFault (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) = none)
    (hw : winners X (sys.active mask) (c.popE l.entry) l.entry = .ok ws)
    (hp : phase2 X (c.popE l.entry) l.entry ws c.machines = .ok (ms, bs))
    (hdup : Dup (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1)
      ((c.popE l.entry).commit sys.sig.machines ms bs) c'') :
    Step sys mask c l (.run mask c'') := by
  subst hX; exact Step.deliverOk hd hr hdr hn hw hp hdup

/-- `Step.deliverErr` with the system of the draws named. -/
theorem Step.deliverErr_via {sys : Sys} {mask : List Bool} {c : Cfg} {l : Label} {X : Sys}
    (hX : sys.resolve l.draws = X)
    (hd : DrawsOk sys l.draws) (hr : Ready sys c l.entry)
    (hdr : ¬ dropHit (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1))
    (hn : delayFault (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) = none)
    (hf : Fails X (sys.active mask) (c.popE l.entry) l.entry (c.attemptsOf l.entry.event + 1)) :
    Step sys mask c l (.err mask c) := by
  subst hX; exact Step.deliverErr hd hr hdr hn hf

section
variable {sys : Sys} (π : MPerm sys.sig.machines)

theorem drawsOk_renameFull {ds : List Nat} : DrawsOk (sys.renameFull π) ds ↔ DrawsOk sys ds := by
  simp only [DrawsOk, dists_renameFull]

theorem ready_renameFull {c : Cfg} {e : Entry} :
    Ready (sys.renameFull π) (c.renameFull π) (e.rename π) ↔ Ready sys c e := by
  simp only [Ready, Cfg.renameFull, mem_map_rename, List.forall_mem_map, Entry.rename_time]

theorem step_rename {mask : List Bool} {c : Cfg} {l : Label} {t : State}
    (hl : c.machines.length = sys.sig.machines) (h : Step sys mask c l t) :
    ∃ t', Step (sys.renameFull π) mask (c.renameFull π) (l.rename π) t' ∧ t'.Approx (t.renameFull π) := by
  have hact : (sys.renameFull π).active mask = renameAct π (sys.active mask) := active_renameFull sys π mask
  have hpop := Cfg.popE_renameFull π c l.entry
  have hatt : (c.renameFull π).attemptsOf (l.rename π).entry.event = c.attemptsOf l.entry.event := rfl
  have hlp : (c.popE l.entry).machines.length = sys.sig.machines := hl
  cases h with
  | drop hd hr hdr =>
    refine ⟨_, Step.drop ((drawsOk_renameFull π).mpr hd) ((ready_renameFull π).mpr hr)
      (by rw [hact, hatt]; exact (dropHit_rename π _ _ _).mpr hdr), ?_⟩
    show State.Approx (.run mask _) (.run mask _)
    rw [Label.rename, ← hpop]
    exact ⟨rfl, Cfg.Approx.refl _⟩
  | delay hd hr hdr hf hlt =>
    refine ⟨_, Step.delay ((drawsOk_renameFull π).mpr hd) ((ready_renameFull π).mpr hr)
      (by rw [hact, hatt]; exact fun h' => hdr ((dropHit_rename π _ _ _).mp h'))
      (by rw [hact, hatt]; simp only [Label.rename]; rw [delayFault_rename, hf]; rfl)
      (by simp only [Label.rename, Fault.rename]; rw [later_rename, hlt]; rfl), ?_⟩
    show State.Approx (.run mask _) (.run mask _)
    simp only [Label.rename]
    rw [← hpop, ← Cfg.enq_renameFull]
    exact ⟨rfl, Cfg.Approx.refl _⟩
  | delayTimeErr hd hr hdr hf hlt =>
    refine ⟨_, Step.delayTimeErr ((drawsOk_renameFull π).mpr hd) ((ready_renameFull π).mpr hr)
      (by rw [hact, hatt]; exact fun h' => hdr ((dropHit_rename π _ _ _).mp h'))
      (by rw [hact, hatt]; simp only [Label.rename]; rw [delayFault_rename, hf]; rfl)
      (by simp only [Label.rename, Fault.rename]; rw [later_rename, hlt]; rfl), ?_⟩
    exact ⟨rfl, Cfg.Approx.refl _⟩
  | deliverOk hd hr hdr hnone hw hp2 hdup =>
    rename_i ws ms bs c''
    have hR := resolve_renameFull sys π l.draws
    obtain ⟨ws', hw', hperm⟩ := winners_rename_fwd (R := sys.resolve l.draws) π hlp hw
    have hnd := winners_nodup hw
    obtain ⟨r2, hr2, hcommit⟩ := phase2_perm_ok (R := sys.resolve l.draws) (c0 := c.popE l.entry) hperm.symm hnd hp2
    have hp2' := phase2_rename (sys := sys.resolve l.draws) π l.entry hlp ws' (c.popE l.entry).machines hl
    rw [hr2] at hp2'
    obtain ⟨c2', hd2, hc2⟩ := Dup.rename π (c1' := ((c.popE l.entry).renameFull π).commit sys.sig.machines
      (permList π r2.1) (Emitted.rename π r2.2)) (by
        have := commit_rename π (c.popE l.entry) r2.1 r2.2
        rw [show (c.popE l.entry).commit sys.sig.machines r2.1 r2.2 =
          (c.popE l.entry).commit sys.sig.machines ms bs from hcommit] at this
        exact this) hdup
    refine ⟨.run mask c2', Step.deliverOk_via (l := l.rename π) (ws := ws') (ms := permList π r2.1) (bs := Emitted.rename π r2.2) hR ((drawsOk_renameFull π).mpr hd)
      ((ready_renameFull π).mpr hr) ?_ ?_ ?_ ?_ ?_, rfl, hc2⟩
    · rw [hact, hatt]; exact fun h' => hdr ((dropHit_rename π _ _ _).mp h')
    · rw [hact, hatt]; simp only [Label.rename]; rw [delayFault_rename, hnone]; rfl
    · rw [hact]; simp only [Label.rename]; rw [← hpop]; exact hw'
    · simp only [Label.rename]; rw [← hpop]; exact hp2'
    · rw [hact, hatt]; simp only [Label.rename]; rw [← hpop]; exact hd2
  | deliverErr hd hr hdr hnone hfail =>
    have hR := resolve_renameFull sys π l.draws
    refine ⟨.err mask (c.renameFull π), Step.deliverErr_via (l := l.rename π) hR ((drawsOk_renameFull π).mpr hd)
      ((ready_renameFull π).mpr hr) ?_ ?_ ?_, rfl, Cfg.Approx.refl _⟩
    · rw [hact, hatt]; exact fun h' => hdr ((dropHit_rename π _ _ _).mp h')
    · rw [hact, hatt]; simp only [Label.rename]; rw [delayFault_rename, hnone]; rfl
    · rw [hact, hatt]; simp only [Label.rename]; rw [← hpop]
      cases hfail with
      | winners hw =>
        obtain ⟨err', h'⟩ := (winners_rename_err (R := sys.resolve l.draws) π hlp).mpr ⟨_, hw⟩
        exact Fails.winners h'
      | phase2 hw hp2 =>
        obtain ⟨ws', hw', hperm⟩ := winners_rename_fwd (R := sys.resolve l.draws) π hlp hw
        obtain ⟨err', h2⟩ := phase2_perm_err hperm.symm (winners_nodup hw) hp2
        have hp2' := phase2_rename (sys := sys.resolve l.draws) π l.entry hlp ws' (c.popE l.entry).machines hl
        rw [h2] at hp2'
        exact Fails.phase2 hw' hp2'
      | dup hw hp2 h0 hl0 =>
        obtain ⟨ws', hw', hperm⟩ := winners_rename_fwd (R := sys.resolve l.draws) π hlp hw
        obtain ⟨r2, hr2, -⟩ := phase2_perm_ok hperm.symm (winners_nodup hw) hp2
        have hp2' := phase2_rename (sys := sys.resolve l.draws) π l.entry hlp ws' (c.popE l.entry).machines hl
        rw [hr2] at hp2'
        exact Fails.dup hw' hp2' (by rw [dupFault_rename, h0]; rfl)
          (by simp only [Fault.rename]; rw [later_rename, hl0]; rfl)

end

/-! ### A step of the renamed system is a renamed step -/

theorem winners_phase2_via {sys : Sys} {act : List (Nat × Fault)} {c0 : Cfg} {e : Entry} {ms0 : List MState}
    {ds : List Nat} {X : Sys} (hX : sys.resolve ds = X) {ws : List (Winner (sys.resolve ds))}
    {r : List MState × Emitted} (hw : winners (sys.resolve ds) act c0 e = .ok ws)
    (hp : phase2 (sys.resolve ds) c0 e ws ms0 = .ok r) :
    ∃ ws' : List (Winner X), winners X act c0 e = .ok ws' ∧ phase2 X c0 e ws' ms0 = .ok r := by
  subst hX; exact ⟨ws, hw, hp⟩

theorem fails_via {sys : Sys} {act : List (Nat × Fault)} {c0 : Cfg} {e : Entry} {att : Nat}
    {ds : List Nat} {X : Sys} (hX : sys.resolve ds = X) (h : Fails (sys.resolve ds) act c0 e att) :
    Fails X act c0 e att := by
  subst hX; exact h

theorem delayFault_unrename {n : Nat} (π : MPerm n) {act : List (Nat × Fault)} {e : Entry} {att i : Nat}
    {f : Fault} (h : delayFault (renameAct π act) (e.rename π) att = some (i, f)) :
    ∃ f0, delayFault act e att = some (i, f0) ∧ f = f0.rename π := by
  rw [delayFault_rename] at h
  cases h0 : delayFault act e att with
  | none => rw [h0] at h; cases h
  | some p =>
    rw [h0] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨p.2, by rw [← h.1], h.2.symm⟩

theorem dupFault_unrename {n : Nat} (π : MPerm n) {act : List (Nat × Fault)} {e : Entry} {att i : Nat}
    {f : Fault} (h : dupFault (renameAct π act) (e.rename π) att = some (i, f)) :
    ∃ f0, dupFault act e att = some (i, f0) ∧ f = f0.rename π := by
  rw [dupFault_rename] at h
  cases h0 : dupFault act e att with
  | none => rw [h0] at h; cases h
  | some p =>
    rw [h0] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨p.2, by rw [← h.1], h.2.symm⟩

theorem delayFault_none_unrename {n : Nat} (π : MPerm n) {act : List (Nat × Fault)} {e : Entry} {att : Nat}
    (h : delayFault (renameAct π act) (e.rename π) att = none) : delayFault act e att = none := by
  rw [delayFault_rename] at h
  cases h0 : delayFault act e att with
  | none => rfl
  | some p => rw [h0] at h; cases h

section
variable {sys : Sys} (π : MPerm sys.sig.machines)

theorem step_unrename {mask : List Bool} {c : Cfg} {l : Label} {t' : State}
    (hl : c.machines.length = sys.sig.machines)
    (h : Step (sys.renameFull π) mask (c.renameFull π) (l.rename π) t') :
    ∃ t, Step sys mask c l t ∧ t'.Approx (t.renameFull π) := by
  have hact : (sys.renameFull π).active mask = renameAct π (sys.active mask) := active_renameFull sys π mask
  have hpop := Cfg.popE_renameFull π c l.entry
  have hatt : (c.renameFull π).attemptsOf (l.rename π).entry.event = c.attemptsOf l.entry.event := rfl
  have hlp : (c.popE l.entry).machines.length = sys.sig.machines := hl
  have hent : (l.rename π).entry = l.entry.rename π := rfl
  cases h with
  | drop hd hr hdr =>
    rw [hact, hatt, hent] at hdr
    refine ⟨_, Step.drop ((drawsOk_renameFull π).mp hd) ((ready_renameFull π).mp hr)
      ((dropHit_rename π _ _ _).mp hdr), ?_⟩
    show State.Approx (.run mask _) (.run mask _)
    rw [hent, ← hpop]
    exact ⟨rfl, Cfg.Approx.refl _⟩
  | delay hd hr hdr hf hlt =>
    rename_i i f cp
    rw [hact, hatt, hent] at hdr hf
    obtain ⟨f0, hf0, rfl⟩ := delayFault_unrename π hf
    rw [hent] at hlt
    simp only [Fault.rename] at hlt
    rw [later_rename] at hlt
    obtain ⟨cp0, hcp0, rfl⟩ := rmap_eq_ok hlt
    refine ⟨_, Step.delay ((drawsOk_renameFull π).mp hd) ((ready_renameFull π).mp hr)
      (fun h' => hdr ((dropHit_rename π _ _ _).mpr h')) hf0 hcp0, ?_⟩
    show State.Approx (.run mask _) (.run mask _)
    rw [hent, ← hpop, ← Cfg.enq_renameFull]
    exact ⟨rfl, Cfg.Approx.refl _⟩
  | delayTimeErr hd hr hdr hf hlt =>
    rename_i i f err
    rw [hact, hatt, hent] at hdr hf
    obtain ⟨f0, hf0, rfl⟩ := delayFault_unrename π hf
    rw [hent] at hlt
    simp only [Fault.rename] at hlt
    rw [later_rename] at hlt
    refine ⟨_, Step.delayTimeErr ((drawsOk_renameFull π).mp hd) ((ready_renameFull π).mp hr)
      (fun h' => hdr ((dropHit_rename π _ _ _).mpr h')) hf0 (rmap_eq_error hlt), ?_⟩
    exact ⟨rfl, Cfg.Approx.refl _⟩
  | deliverOk hd hr hdr hnone hw hp2 hdup =>
    rename_i ws' ms' bs' c2'
    have hR := resolve_renameFull sys π l.draws
    obtain ⟨ws2, hw2, hp22⟩ := winners_phase2_via (ds := l.draws) hR hw hp2
    rw [hact, hatt, hent] at hdr hnone hdup
    rw [hact, hent, ← hpop] at hw2
    rw [hent, ← hpop] at hp22
    rw [← hpop] at hdup
    obtain ⟨ws, hws, hperm⟩ := winners_rename_bwd (R := sys.resolve l.draws) π hlp hw2
    have hp2' := phase2_rename (sys := sys.resolve l.draws) π l.entry hlp ws2 (c.popE l.entry).machines hl
    obtain ⟨r2, hr2, hr2eq⟩ := rmap_eq_ok (hp2'.symm.trans hp22)
    have hnd := winners_nodup_back (R := sys.resolve l.draws) π hws hperm
    obtain ⟨⟨ms3, bs3⟩, hr3, hc3⟩ := phase2_perm_ok (R := sys.resolve l.draws) hperm hnd hr2
    simp only [Prod.mk.injEq] at hr2eq
    obtain ⟨rfl, rfl⟩ := hr2eq
    have happ : (((c.popE l.entry).renameFull π).commit sys.sig.machines (permList π r2.1)
        (Emitted.rename π r2.2)).Approx
        (((c.popE l.entry).commit sys.sig.machines ms3 bs3).renameFull π) := by
      have := commit_rename π (c.popE l.entry) r2.1 r2.2
      rw [show (c.popE l.entry).commit sys.sig.machines ms3 bs3 =
        (c.popE l.entry).commit sys.sig.machines r2.1 r2.2 from hc3]
      exact this
    obtain ⟨c2, hd2, hc2⟩ := Dup.unrename π happ hdup
    refine ⟨.run mask c2, Step.deliverOk ((drawsOk_renameFull π).mp hd) ((ready_renameFull π).mp hr)
      (fun h' => hdr ((dropHit_rename π _ _ _).mpr h')) (delayFault_none_unrename π hnone) hws hr3 hd2,
      rfl, hc2⟩
  | deliverErr hd hr hdr hnone hfail =>
    have hR := resolve_renameFull sys π l.draws
    have hf2 := fails_via (ds := l.draws) hR hfail
    rw [hact, hatt, hent] at hdr hnone hf2
    rw [← hpop] at hf2
    refine ⟨.err mask c, Step.deliverErr ((drawsOk_renameFull π).mp hd) ((ready_renameFull π).mp hr)
      (fun h' => hdr ((dropHit_rename π _ _ _).mpr h')) (delayFault_none_unrename π hnone) ?_,
      rfl, Cfg.Approx.refl _⟩
    cases hf2 with
    | winners hw =>
      obtain ⟨err', h'⟩ := (winners_rename_err (R := sys.resolve l.draws) π hlp).mp ⟨_, hw⟩
      exact Fails.winners h'
    | phase2 hw hp =>
      rename_i ws2 err
      obtain ⟨ws, hws, hperm⟩ := winners_rename_bwd (R := sys.resolve l.draws) π hlp hw
      have hp2' := phase2_rename (sys := sys.resolve l.draws) π l.entry hlp ws2 (c.popE l.entry).machines hl
      have h2 := rmap_eq_error (hp2'.symm.trans hp)
      obtain ⟨err', h3⟩ := phase2_perm_err (R := sys.resolve l.draws) hperm (winners_nodup_back (R := sys.resolve l.draws) π hws hperm) h2
      exact Fails.phase2 hws h3
    | dup hw hp h0 hl0 =>
      rename_i ws2 ms2 bs2 i f err
      obtain ⟨ws, hws, hperm⟩ := winners_rename_bwd (R := sys.resolve l.draws) π hlp hw
      have hp2' := phase2_rename (sys := sys.resolve l.draws) π l.entry hlp ws2 (c.popE l.entry).machines hl
      obtain ⟨r2, hr2, -⟩ := rmap_eq_ok (hp2'.symm.trans hp)
      obtain ⟨⟨ms3, bs3⟩, hr3, -⟩ := phase2_perm_ok (R := sys.resolve l.draws) hperm
        (winners_nodup_back (R := sys.resolve l.draws) π hws hperm) hr2
      obtain ⟨f0, hf0, rfl⟩ := dupFault_unrename π h0
      simp only [Fault.rename] at hl0
      rw [later_rename] at hl0
      exact Fails.dup hws hr3 hf0 (rmap_eq_error hl0)

end

/-! ### Equality up to the order of the pending list -/

theorem Cfg.Approx.trans {a b c : Cfg} (h1 : a.Approx b) (h2 : b.Approx c) : a.Approx c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem State.Approx.symm {s t : State} (h : s.Approx t) : t.Approx s := by
  cases s <;> cases t <;> simp only [State.Approx] at h ⊢
  all_goals first | exact h | exact ⟨h.1.symm, Cfg.Approx.symm h.2⟩

theorem State.Approx.trans {s t u : State} (h1 : s.Approx t) (h2 : t.Approx u) : s.Approx u := by
  cases s <;> cases t <;> cases u <;> simp only [State.Approx] at h1 h2 ⊢
  all_goals first | exact h1.elim | exact h2.elim | exact ⟨h1.1.trans h2.1, Cfg.Approx.trans h1.2 h2.2⟩

theorem State.Approx.refl (s : State) : s.Approx s := by
  cases s <;> exact ⟨rfl, Cfg.Approx.refl _⟩

theorem Cfg.Approx.renameFull {n : Nat} (π : MPerm n) {c c' : Cfg} (h : c.Approx c') :
    (c.renameFull π).Approx (c'.renameFull π) :=
  ⟨h.1, by simp only [Cfg.renameFull, h.2.1], h.2.2.1, h.2.2.2.map _⟩

theorem State.Approx.renameFull {n : Nat} (π : MPerm n) {s s' : State} (h : s.Approx s') :
    (s.renameFull π).Approx (s'.renameFull π) := by
  cases s <;> cases s' <;> simp only [State.Approx, State.renameFull] at h ⊢
  all_goals first | exact h | exact ⟨h.1, Cfg.Approx.renameFull π h.2⟩

theorem Entry.rename_inv {n : Nat} (π : MPerm n) (e : Entry) : (e.rename π).rename π⁻¹ = e := by
  obtain ⟨t, ev, p, g, m, d, s⟩ := e
  simp only [Entry.rename, Option.map_map, Function.comp_def, π.inv_nat_nat, Option.map_id']

theorem Cfg.renameFull_inv {n : Nat} (π : MPerm n) {c : Cfg} (hl : c.machines.length = n) :
    (c.renameFull π).renameFull π⁻¹ = c := by
  simp only [Cfg.renameFull, permList_inv π hl, List.map_map, Function.comp_def, Entry.rename_inv,
    List.map_id']

theorem State.renameFull_inv {n : Nat} (π : MPerm n) {s : State} (hl : s.cfg.machines.length = n) :
    (s.renameFull π).renameFull π⁻¹ = s := by
  cases s <;> simp only [State.renameFull, State.cfg] at hl ⊢ <;> rw [Cfg.renameFull_inv π hl]

theorem State.Approx.length {s t : State} (h : s.Approx t) : s.cfg.machines.length = t.cfg.machines.length := by
  cases s <;> cases t <;> simp only [State.Approx] at h <;> first | exact h.elim | simp only [State.cfg, h.2.2.1]

theorem State.rename_of_length {n : Nat} (π : MPerm n) {s : State} (hl : s.cfg.machines.length = n) :
    s.rename π = s.renameFull π := by
  cases s <;> simp only [State.cfg] at hl <;> simp [State.rename, State.renameFull, Cfg.rename, hl]

theorem State.rename_of_ne {n : Nat} (π : MPerm n) {s : State} (hl : s.cfg.machines.length ≠ n) :
    s.rename π = s := by
  cases s <;> simp only [State.cfg] at hl <;> simp [State.rename, Cfg.rename, hl]

@[simp] theorem State.renameFull_length {n : Nat} (π : MPerm n) (s : State) :
    (s.renameFull π).cfg.machines.length = n := by
  cases s <;> simp [State.renameFull, State.cfg, Cfg.renameFull]

/-! ### The number of machines is constant along steps -/

theorem phase2_length {sys : Sys} {c : Cfg} {e : Entry} : (ws : List (Winner sys)) → (ms : List MState) →
    {r : List MState × Emitted} → phase2 sys c e ws ms = .ok r → r.1.length = ms.length
  | [], ms, r, h => by simp only [phase2] at h; cases h; rfl
  | w :: ws, ms, r, h => by
    simp only [phase2] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i st out _ ms' outs hp
          cases h
          have := phase2_length ws _ hp
          simp only [List.length_set] at this
          exact this

theorem Dup.machines {act : List (Nat × Fault)} {e : Entry} {att : Nat} {c1 c2 : Cfg}
    (h : Dup act e att c1 c2) : c2.machines = c1.machines := by
  cases h <;> rfl

theorem step_length {sys : Sys} {m : List Bool} {c : Cfg} {l : Label} {t : State}
    (h : Step sys m c l t) : t.cfg.machines.length = c.machines.length := by
  cases h with
  | drop => rfl
  | delay => rfl
  | delayTimeErr => rfl
  | deliverOk _ _ _ _ _ hp hd =>
    simp only [State.cfg]
    rw [Dup.machines hd]
    exact phase2_length _ _ hp
  | deliverErr => rfl

theorem reach_length {sys : Sys} {s : State} (h : (Sys.lts sys).Reach s) :
    s.cfg.machines.length = sys.init.machines.length := by
  induction h with
  | init hi =>
    obtain ⟨mask, -, rfl⟩ := hi
    rfl
  | step _ hst ih =>
    rename_i s t a _
    cases s with
    | err => exact absurd hst id
    | run m c => rw [step_length (show Step sys m c a t from hst)]; exact ih

/-! ### The initial states -/

theorem injectStep_rename {n : Nat} (π : MPerm n) (q : List Entry) (p : Nat × Fault) :
    injectStep (q.map (Entry.rename π)) (p.1, p.2.rename π) = (injectStep q p).map (Entry.rename π) := by
  unfold injectStep
  by_cases hk : p.2.kind = .inject
  · simp only [Fault.rename, hk, ↓reduceIte]
    exact insertByTime_rename π { time := p.2.at_, event := p.2.event, payload := p.2.payload } q
  · simp only [Fault.rename, hk, ↓reduceIte]

theorem foldl_injectStep_rename {n : Nat} (π : MPerm n) : (act : List (Nat × Fault)) → (q : List Entry) →
    (renameAct π act).foldl injectStep (q.map (Entry.rename π)) =
      (act.foldl injectStep q).map (Entry.rename π)
  | [], q => rfl
  | p :: act, q => by
    simp only [renameAct, List.map_cons, List.foldl_cons] at *
    rw [injectStep_rename]
    exact foldl_injectStep_rename π act _

theorem initCfg_renameFull (sys : Sys) (π : MPerm sys.sig.machines) (mask : List Bool) :
    (sys.renameFull π).initCfg mask = (sys.initCfg mask).renameFull π := by
  unfold Sys.initCfg
  rw [active_renameFull]
  simp only [Cfg.renameFull]
  rw [← foldl_injectStep_rename]

/-! ### Reachability in the two systems -/

section
variable {sys : Sys} (π : MPerm sys.sig.machines)

theorem reach_renameFull (hlen : sys.init.machines.length = sys.sig.machines) {s : State}
    (h : (Sys.lts sys).Reach s) :
    ∃ s', (Sys.lts (sys.renameFull π)).Reach s' ∧ s'.Approx (s.renameFull π) := by
  induction h with
  | init hi =>
    obtain ⟨mask, hm, rfl⟩ := hi
    refine ⟨_, .init ⟨mask, by simpa [Sys.renameFull] using hm, rfl⟩, ?_⟩
    rw [initCfg_renameFull]
    exact State.Approx.refl _
  | step hr hst ih =>
    rename_i s t a
    obtain ⟨s', hs', hap⟩ := ih
    have hl := (reach_length hr).trans hlen
    cases s with
    | err => exact absurd hst id
    | run m c =>
      obtain ⟨t1, ht1, ht1a⟩ := step_rename π hl (show Step sys m c a t from hst)
      cases s' with
      | err => exact hap.elim
      | run m' c' =>
        obtain ⟨rfl, hca⟩ := hap
        obtain ⟨t2, ht2, ht2a⟩ := pending_perm_bisim hca.2.2.2.symm hca.1.symm hca.2.1.symm hca.2.2.1.symm ht1
        exact ⟨t2, .step hs' ht2, ht2a.trans ht1a⟩

theorem reach_unrename (hlen : sys.init.machines.length = sys.sig.machines) {s' : State}
    (h : (Sys.lts (sys.renameFull π)).Reach s') :
    ∃ s, (Sys.lts sys).Reach s ∧ s'.Approx (s.renameFull π) := by
  induction h with
  | init hi =>
    obtain ⟨mask, hm, rfl⟩ := hi
    refine ⟨.run mask (sys.initCfg mask), .init ⟨mask, by simpa [Sys.renameFull] using hm, rfl⟩, ?_⟩
    rw [initCfg_renameFull]
    exact State.Approx.refl _
  | step _ hst ih =>
    rename_i s' t' a' _
    obtain ⟨s, hs, hap⟩ := ih
    have hl := (reach_length hs).trans hlen
    cases s with
    | err m c =>
      cases s' with
      | run => exact hap.elim
      | err => exact absurd hst id
    | run m c =>
      cases s' with
      | err => exact hap.elim
      | run m' c' =>
        obtain ⟨rfl, hca⟩ := hap
        have hst' : Step (sys.renameFull π) _ c' a' t' := hst
        obtain ⟨t1, ht1, ht1a⟩ := pending_perm_bisim hca.2.2.2 hca.1 hca.2.1 hca.2.2.1 hst'
        obtain ⟨-, hrdy⟩ := Step.ready ht1
        obtain ⟨e, -, he⟩ := List.mem_map.mp hrdy.1
        have hlab : a' = Label.rename π ⟨e, a'.draws⟩ := by
          cases a'; simp only [Label.rename] at he ⊢; rw [he]
        rw [hlab] at ht1
        obtain ⟨t, ht, hta⟩ := step_unrename π hl ht1
        exact ⟨t, .step hs ht, ht1a.symm.trans hta⟩

end

/-! ### One verdict, in general -/

/-- **One verdict, in general** (the task's criterion 8; replaces reliance on the `[a, b]` /
`[b, a]` example). For every permutation `π` of the machine indices and every property `P` that
does not distinguish states equal up to the order of the pending list, `P` is an invariant of
`sys` exactly when `P ∘ State.rename π⁻¹` is an invariant of `sys.rename π`, the system listing
its machines in the order `π`. -/
theorem invariant_rename {sys : Sys} (π : MPerm sys.sig.machines) {P : State → Prop}
    (hP : ∀ s s', s.Approx s' → (P s ↔ P s')) :
    (Sys.lts sys).Invariant P ↔ (Sys.lts (sys.rename π)).Invariant (P ∘ State.rename π⁻¹) := by
  by_cases hlen : sys.init.machines.length = sys.sig.machines
  · have hsys : sys.rename π = sys.renameFull π := by simp [Sys.rename, hlen]
    rw [hsys]
    -- the inverse renaming undoes the renaming up to the order of the pending list
    have hback : ∀ s s', (Sys.lts sys).Reach s → s'.Approx (s.renameFull π) →
        (State.rename π⁻¹ s').Approx s := by
      intro s s' hs hap
      have hl := (reach_length hs).trans hlen
      have hl' : s'.cfg.machines.length = sys.sig.machines := by
        rw [hap.length]; exact State.renameFull_length π s
      rw [State.rename_of_length π⁻¹ hl']
      have := State.Approx.renameFull π⁻¹ hap
      rw [State.renameFull_inv π hl] at this
      exact this
    constructor
    · intro hinv s' hs'
      obtain ⟨s, hs, hap⟩ := reach_unrename π hlen hs'
      exact (hP _ _ (hback s s' hs hap)).mpr (hinv s hs)
    · intro hinv s hs
      obtain ⟨s', hs', hap⟩ := reach_renameFull π hlen hs
      exact (hP _ _ (hback s s' hs hap)).mp (hinv s' hs')
  · have hsys : sys.rename π = sys := by simp [Sys.rename, hlen]
    rw [hsys]
    constructor
    · intro hinv s hs
      have hl : s.cfg.machines.length ≠ sys.sig.machines := by rw [reach_length hs]; exact hlen
      show P (State.rename π⁻¹ s)
      rw [State.rename_of_ne π⁻¹ hl]
      exact hinv s hs
    · intro hinv s hs
      have hl : s.cfg.machines.length ≠ sys.sig.machines := by rw [reach_length hs]; exact hlen
      have := hinv s hs
      simp only [Function.comp_def] at this
      rw [State.rename_of_ne π⁻¹ hl] at this
      exact this

end Exegra.Core.Behav

/-- info: 'Exegra.Core.Behav.invariant_rename' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.invariant_rename

/-- info: 'Exegra.Core.Behav.step_rename' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.step_rename
