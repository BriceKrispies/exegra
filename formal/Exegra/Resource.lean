/-
Resources of format 2 (`docs/simulation.md`, "Resources"): pools of identical units with request
classes, reservations, class limits, queue bounds and overflow rules, and the invariants of a
settled resource.

This module is the pure algebra of one resource: the holdings, the waiting list, the grant loop
and the bounds step. The step semantics (`Exegra/Semantics2.lean`) records `use`, `acquire` and
`release` effects in phase 2 and settles each touched resource with these functions, turning
their outcomes (grants, refusals, drops) into queue entries and trace records.

* The waiting list is kept in arrival order, which is `(since, seq)` order: requests are appended
  with `since = now` and a fresh `seq`, and time never decreases. A class queue is the waiting list
  filtered to that class, so service within a class is FIFO.
* A request's `id` is its sequence number.
* `Hold`s record units held: a `use` holds them for its service (`req = some id`), an `acquire`
  until `release` (`req = none`).

Proved below, with no `sorry`: the grant loop keeps `held(class) ≤ limit(class)` and
`Σ held ≤ capacity`, releases never raise them, and after the bounds step every class queue and the
whole waiting list are within their bounds.
-/

namespace Exegra.Res

variable {κ : Type}

inductive Overflow where
  | refuse | drop | shedOldest
  deriving DecidableEq, Inhabited

structure ClassDecl where
  id : String
  priority : Int
  reserved : Nat
  limit : Option Nat
  queueBound : Option Nat
  maxWait : Option Nat
  deriving Inhabited

/-- Load-dependent demand factor: none, a step table `[n, num, den]`, or USL parameters
`alpha = an/ad`, `beta = bn/bd`. -/
inductive DemandFactor where
  | none
  | table (rows : List (Nat × Nat × Nat))
  | usl (an ad bn bd : Nat)
  deriving Inhabited

structure ResourceDecl where
  id : String
  kind : String
  capacity : Nat
  /-- `discipline: "priority"`; otherwise `fifo`. -/
  byPriority : Bool
  queueBound : Option Nat
  overflow : Overflow
  demandFactor : DemandFactor
  classes : List ClassDecl
  /-- One strict FIFO queue (a `collapse-classes` fault): the oldest head is granted or nothing. -/
  strict : Bool := false
  deriving Inhabited

def ResourceDecl.classAt? (d : ResourceDecl) (i : Nat) : Option ClassDecl := d.classes[i]?

def ResourceDecl.limitOf (d : ResourceDecl) (i : Nat) : Option Nat :=
  (d.classAt? i).bind (·.limit)

def ResourceDecl.reservedOf (d : ResourceDecl) (i : Nat) : Nat :=
  ((d.classAt? i).map (·.reserved)).getD 0

def ResourceDecl.priorityOf (d : ResourceDecl) (i : Nat) : Int :=
  ((d.classAt? i).map (·.priority)).getD 0

/-- The demand factor `num/den` at occupancy `o`. -/
def DemandFactor.at (f : DemandFactor) (o : Nat) : Nat × Nat :=
  match f with
  | .none => (1, 1)
  | .table rows =>
    rows.foldl (fun acc (n, num, den) => if n ≤ o then (num, den) else acc) (1, 1)
  | .usl an ad bn bd =>
    -- f(n) = 1 + alpha·(n − 1) + beta·n·(n − 1), n ≥ 1
    let n := max o 1
    (ad * bd + an * bd * (n - 1) + bn * ad * n * (n - 1), ad * bd)

inductive ReqKind where
  | use | acquire
  deriving DecidableEq, Inhabited, Repr, Hashable

/-- A waiting request; `α` is what the semantics needs to answer it. -/
structure Req (κ α : Type) where
  id : Nat
  owner : κ
  cls : Nat
  units : Nat
  since : Nat
  kind : ReqKind
  info : α
  deriving DecidableEq, Repr, Hashable

structure Hold (κ : Type) where
  owner : κ
  cls : Nat
  units : Nat
  /-- The `use` request these units serve; `none` for `acquire`. -/
  req : Option Nat
  deriving DecidableEq, Repr, Hashable

structure RState (κ α : Type) where
  capacity : Nat
  holds : List (Hold κ)
  waiting : List (Req κ α)
  deriving DecidableEq, Repr, Hashable

/-! ## Sums -/

def sumUnits (p : Hold κ → Bool) : List (Hold κ) → Nat
  | [] => 0
  | h :: hs => (if p h then h.units else 0) + sumUnits p hs

theorem sumUnits_append (p : Hold κ → Bool) (xs ys : List (Hold κ)) :
    sumUnits p (xs ++ ys) = sumUnits p xs + sumUnits p ys := by
  induction xs with
  | nil => simp [sumUnits]
  | cons x xs ih => simp [sumUnits, ih]; omega

def heldC (hs : List (Hold κ)) (c : Nat) : Nat := sumUnits (fun h => h.cls == c) hs
def heldAll (hs : List (Hold κ)) : Nat := sumUnits (fun _ => true) hs
def heldBy [BEq κ] (hs : List (Hold κ)) (owner : κ) (c : Nat) : Nat :=
  sumUnits (fun h => h.owner == owner && h.cls == c && h.req.isNone) hs

def waitingC {κ α} (ws : List (Req κ α)) (c : Nat) : Nat := ws.countP (fun r => r.cls == c)

/-! ## Eligibility and choice -/

/-- Units other classes still have reserved and unused: `Σ_{k ≠ c} max(0, reserved(k) − held(k))`. -/
def shortfall (d : ResourceDecl) (hs : List (Hold κ)) (c : Nat) : Nat :=
  ((List.range d.classes.length).filter (· != c)).foldl
    (fun acc k => acc + (d.reservedOf k - heldC hs k)) 0

/-- A head fits: within its class limit and within the free units not reserved by other classes. -/
def fits {κ α} (d : ResourceDecl) (s : RState κ α) (r : Req κ α) : Bool :=
  (match d.limitOf r.cls with
   | none => true
   | some l => decide (heldC s.holds r.cls + r.units ≤ l)) &&
  decide (r.units ≤ s.capacity - heldAll s.holds - shortfall d s.holds r.cls)

/-- Is `a` served before `b`? Priority: higher priority, then older head, then lower seq; FIFO:
older, then lower seq. -/
def before {κ α} (d : ResourceDecl) (a b : Req κ α) : Bool :=
  let older := a.since < b.since || (a.since == b.since && a.id < b.id)
  if d.byPriority then
    let pa := d.priorityOf a.cls
    let pb := d.priorityOf b.cls
    pa > pb || (pa == pb && older)
  else older

/-- The next request to grant: the best eligible class head. -/
def pickAmong {κ α} (d : ResourceDecl) (s : RState κ α) (heads : List (Req κ α)) : Option (Req κ α) :=
  (heads.filter (fits d s)).foldl (fun acc r =>
    match acc with
    | none => some r
    | some b => if before d r b then some r else some b) none

/-- Strict FIFO: the oldest head, if it fits. -/
def pickStrict {κ α} (d : ResourceDecl) (s : RState κ α) (heads : List (Req κ α)) : Option (Req κ α) :=
  match heads.foldl (fun acc r =>
      match acc with
      | none => some r
      | some b => if before d r b then some r else some b) none with
  | some r => if fits d s r then some r else none
  | none => none

def pick {κ α} (d : ResourceDecl) (s : RState κ α) : Option (Req κ α) :=
  let heads := (List.range d.classes.length).filterMap fun c => s.waiting.find? (·.cls == c)
  if d.strict then pickStrict d s heads else pickAmong d s heads

theorem pickStrict_fits {κ α} {d : ResourceDecl} {s : RState κ α} {heads : List (Req κ α)} {r : Req κ α}
    (h : pickStrict d s heads = some r) : fits d s r = true := by
  unfold pickStrict at h
  split at h
  · split at h
    · simp at h; subst h; assumption
    · simp at h
  · simp at h

theorem pick_fits {κ α} {d : ResourceDecl} {s : RState κ α} {r : Req κ α} (h : pick d s = some r) :
    fits d s r = true := by
  unfold pick at h
  split at h
  · exact pickStrict_fits h
  unfold pickAmong at h
  generalize (List.filterMap _ _) = heads at h
  suffices ∀ (xs : List (Req κ α)) (acc : Option (Req κ α)),
      (∀ b, acc = some b → fits d s b = true) → (∀ x ∈ xs, fits d s x = true) →
      ∀ r, xs.foldl (fun acc r => match acc with
        | none => some r
        | some b => if before d r b then some r else some b) acc = some r → fits d s r = true by
    exact this _ none (by simp) (by intro x hx; exact (List.mem_filter.mp hx).2) r h
  intro xs
  induction xs with
  | nil => intro acc hacc _ r h; exact hacc r h
  | cons x xs ih =>
    intro acc hacc hxs r h
    simp only [List.foldl] at h
    refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) r h
    intro b hb
    have hx := hxs x (List.mem_cons_self ..)
    cases acc with
    | none => simp at hb; exact hb ▸ hx
    | some a =>
      simp only at hb
      split at hb
      · simp at hb; exact hb ▸ hx
      · simp at hb; exact hb ▸ hacc a rfl

/-! ## The grant loop -/

/-- What settling did to a request, in order. `occupancy` is the units held after the grant plus
the requests still waiting at that point. -/
inductive Out (κ α : Type) where
  | granted (r : Req κ α) (occupancy : Nat)
  | refused (r : Req κ α) (shed : Bool)
  | dropped (r : Req κ α)

def grantOne {κ α} (s : RState κ α) (r : Req κ α) : RState κ α :=
  { s with
    waiting := s.waiting.filter (fun w => w.id != r.id),
    holds := s.holds ++ [{ owner := r.owner, cls := r.cls, units := r.units,
                           req := if r.kind == .use then some r.id else none }] }

/-- Grant while some class head is eligible (at most one grant per waiting request). -/
def grantLoop {κ α} (d : ResourceDecl) : Nat → RState κ α → List (Out κ α) → RState κ α × List (Out κ α)
  | 0, s, outs => (s, outs)
  | fuel + 1, s, outs =>
    match pick d s with
    | none => (s, outs)
    | some r =>
      let s' := grantOne s r
      grantLoop d fuel s' (outs ++ [.granted r (heldAll s'.holds + s'.waiting.length)])

/-- The held-units invariant of a resource. -/
def HeldOk {κ α} (d : ResourceDecl) (s : RState κ α) : Prop :=
  heldAll s.holds ≤ s.capacity ∧ ∀ c l, d.limitOf c = some l → heldC s.holds c ≤ l

theorem grantOne_ok {κ α} {d : ResourceDecl} {s : RState κ α} {r : Req κ α}
    (hs : HeldOk d s) (hf : fits d s r = true) : HeldOk d (grantOne s r) := by
  obtain ⟨hall, hcl⟩ := hs
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hlim, hfree⟩ := hf
  refine ⟨?_, ?_⟩
  · simp [grantOne, heldAll, sumUnits_append, sumUnits]
    simp only [heldAll] at hall hfree
    omega
  · intro c l hl
    simp only [grantOne, heldC, sumUnits_append, sumUnits]
    by_cases hc : r.cls = c
    · subst hc
      rw [hl] at hlim
      simp only [decide_eq_true_eq] at hlim
      simp [heldC] at hlim ⊢
      omega
    · have := hcl c l hl
      simp [heldC] at this ⊢
      simp [hc]
      omega

theorem grantLoop_ok {κ α} (d : ResourceDecl) :
    ∀ (fuel : Nat) (s : RState κ α) (outs : List (Out κ α)),
      HeldOk d s → HeldOk d (grantLoop d fuel s outs).1 := by
  intro fuel
  induction fuel with
  | zero => intro s outs h; simpa [grantLoop] using h
  | succ n ih =>
    intro s outs h
    simp only [grantLoop]
    split
    · exact h
    · rename_i r hp
      exact ih _ _ (grantOne_ok h (pick_fits hp))

/-! ## Releases -/

/-- Release `n` acquired units of `(owner, class)`, oldest holdings first. -/
def consume [BEq κ] (owner : κ) (c : Nat) : Nat → List (Hold κ) → List (Hold κ)
  | _, [] => []
  | n, h :: hs =>
    if h.owner == owner && h.cls == c && h.req.isNone then
      let t := min n h.units
      (if h.units - t = 0 then [] else [{ h with units := h.units - t }]) ++ consume owner c (n - t) hs
    else h :: consume owner c n hs

theorem sumUnits_consume (p : Hold κ → Bool) (hpu : ∀ h u, p { h with units := u } = p h)
    [BEq κ] (owner : κ) (c : Nat) :
    ∀ (n : Nat) (hs : List (Hold κ)), sumUnits p (consume owner c n hs) ≤ sumUnits p hs := by
  intro n hs
  induction hs generalizing n with
  | nil => simp [consume, sumUnits]
  | cons h hs ih =>
    simp only [consume]
    split
    · rw [sumUnits_append]
      have := ih (n - min n h.units)
      have hu := hpu h (h.units - min n h.units)
      by_cases hz : h.units - min n h.units = 0 <;> by_cases hp : p h = true <;>
        simp [hz, hp, hu, sumUnits] <;> omega
    · simp only [sumUnits]
      have := ih n
      omega

/-- End the service of a `use` request: its units are released. -/
def endService (rid : Nat) (hs : List (Hold κ)) : List (Hold κ) := hs.filter (fun h => h.req != some rid)

theorem sumUnits_filter (p q : Hold κ → Bool) :
    ∀ hs : List (Hold κ), sumUnits p (hs.filter q) ≤ sumUnits p hs := by
  intro hs
  induction hs with
  | nil => simp [sumUnits]
  | cons h hs ih =>
    simp only [List.filter]
    split <;> simp only [sumUnits] <;> omega

theorem release_ok {κ α} {d : ResourceDecl} {s : RState κ α} (f : List (Hold κ) → List (Hold κ))
    (hfall : heldAll (f s.holds) ≤ heldAll s.holds)
    (hfc : ∀ c, heldC (f s.holds) c ≤ heldC s.holds c) (h : HeldOk d s) :
    HeldOk d { s with holds := f s.holds } := by
  obtain ⟨hall, hcl⟩ := h
  exact ⟨Nat.le_trans hfall hall, fun c l hl => Nat.le_trans (hfc c) (hcl c l hl)⟩

/-- Releasing acquired units keeps the held-units invariant. -/
theorem consume_ok {κ α} [BEq κ] {d : ResourceDecl} {s : RState κ α} (owner : κ) (c n : Nat)
    (h : HeldOk d s) : HeldOk d { s with holds := consume owner c n s.holds } :=
  release_ok _ (sumUnits_consume _ (fun _ _ => rfl) _ _ _ _)
    (fun _ => sumUnits_consume _ (fun _ _ => rfl) _ _ _ _) h

/-- Ending a service keeps the held-units invariant. -/
theorem endService_ok {κ α} {d : ResourceDecl} {s : RState κ α} (rid : Nat)
    (h : HeldOk d s) : HeldOk d { s with holds := endService rid s.holds } :=
  release_ok _ (sumUnits_filter _ _ _) (fun _ => sumUnits_filter _ _ _) h

/-! ## Bounds -/

/-- Take the first element satisfying `p`. -/
def takeFirst {β} (p : β → Bool) : List β → Option (β × List β)
  | [] => none
  | x :: xs => if p x then some (x, xs) else (takeFirst p xs).map fun (y, ys) => (y, x :: ys)

/-- Take the last element satisfying `p`. -/
def takeLast {β} (p : β → Bool) (xs : List β) : Option (β × List β) :=
  (takeFirst p xs.reverse).map fun (y, ys) => (y, ys.reverse)

theorem takeFirst_some {β} (p : β → Bool) :
    ∀ (xs : List β) (y : β) (ys : List β), takeFirst p xs = some (y, ys) →
      p y = true ∧ ∀ q, ys.countP q + (if q y then 1 else 0) = xs.countP q := by
  intro xs
  induction xs with
  | nil => intro y ys h; simp [takeFirst] at h
  | cons x xs ih =>
    intro y ys h
    simp only [takeFirst] at h
    split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨by assumption, fun q => ?_⟩
      simp [List.countP_cons]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨y', ys'⟩, h1, h2⟩ := h
      simp at h2; obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨hp, hc⟩ := ih _ _ h1
      refine ⟨hp, fun q => ?_⟩
      have := hc q
      simp only [List.countP_cons]
      omega

theorem takeFirst_none {β} (p : β → Bool) :
    ∀ xs : List β, takeFirst p xs = none → xs.countP p = 0 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro h
    simp only [takeFirst] at h
    split at h
    · simp at h
    · simp only [Option.map_eq_none_iff] at h
      simp [ih h, *]

theorem takeLast_some {β} (p : β → Bool) (xs : List β) (y : β) (ys : List β)
    (h : takeLast p xs = some (y, ys)) :
    p y = true ∧ ∀ q, ys.countP q + (if q y then 1 else 0) = xs.countP q := by
  simp only [takeLast, Option.map_eq_some_iff] at h
  obtain ⟨⟨y', ys'⟩, h1, h2⟩ := h
  simp at h2; obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨hp, hc⟩ := takeFirst_some p _ _ _ h1
  refine ⟨hp, fun q => ?_⟩
  rw [List.countP_reverse, ← List.countP_reverse (l := xs)]
  exact hc q

theorem takeLast_none {β} (p : β → Bool) (xs : List β) (h : takeLast p xs = none) :
    xs.countP p = 0 := by
  simp only [takeLast, Option.map_eq_none_iff] at h
  rw [← List.countP_reverse]; exact takeFirst_none p _ h

/-- Remove one element at a time with `choose` while `count` exceeds `bound`. -/
def enforce {β} (count : List β → Nat) (bound : Nat) (choose : List β → Option (β × List β)) :
    Nat → List β → List β → List β × List β
  | 0, xs, removed => (xs, removed)
  | fuel + 1, xs, removed =>
    if count xs ≤ bound then (xs, removed) else
    match choose xs with
    | none => (xs, removed)
    | some (r, ys) => enforce count bound choose fuel ys (removed ++ [r])

/-- `enforce` meets its bound when `choose` lowers `count` by one whenever it is positive. -/
theorem enforce_bound {β} (count : List β → Nat) (bound : Nat)
    (choose : List β → Option (β × List β))
    (hnone : ∀ xs, choose xs = none → count xs = 0)
    (hsome : ∀ xs r ys, choose xs = some (r, ys) → count ys + 1 = count xs) :
    ∀ fuel xs removed, count xs ≤ fuel + bound → count (enforce count bound choose fuel xs removed).1 ≤ bound := by
  intro fuel
  induction fuel with
  | zero => intro xs removed h; simpa [enforce] using h
  | succ n ih =>
    intro xs removed h
    simp only [enforce]
    split
    · assumption
    · split
      · rename_i hc; have := hnone _ hc; omega
      · rename_i r ys hc
        have := hsome _ _ _ hc
        exact ih _ _ (by omega)

/-- `enforce` never raises a count that `choose` never raises. -/
theorem enforce_mono {β} (count : List β → Nat) (bound : Nat)
    (choose : List β → Option (β × List β)) (q : List β → Nat)
    (hq : ∀ xs r ys, choose xs = some (r, ys) → q ys ≤ q xs) :
    ∀ fuel xs removed, q (enforce count bound choose fuel xs removed).1 ≤ q xs := by
  intro fuel
  induction fuel with
  | zero => intro xs removed; simp [enforce]
  | succ n ih =>
    intro xs removed
    simp only [enforce]
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · rename_i r ys hc
        exact Nat.le_trans (ih _ _) (hq _ _ _ hc)

/-- Choosing the request removed at a class bound. -/
def chooseClass {κ α} (o : Overflow) (c : Nat) (ws : List (Req κ α)) : Option (Req κ α × List (Req κ α)) :=
  if o == .shedOldest then takeFirst (fun r => r.cls == c) ws else takeLast (fun r => r.cls == c) ws

/-- The class shed first at the resource bound under `priority`: among classes with a waiting
request, the lowest priority, first in declaration order on ties. -/
def lowestClass {κ α} (d : ResourceDecl) (ws : List (Req κ α)) : Option Nat :=
  ((List.range d.classes.length).filter (fun c => ws.any (·.cls == c))).foldl (fun acc c =>
    match acc with
    | none => some c
    | some b => if d.priorityOf c < d.priorityOf b then some c else some b) none

/-- Choosing the request removed at the resource bound. -/
def chooseAll {κ α} (d : ResourceDecl) (ws : List (Req κ α)) : Option (Req κ α × List (Req κ α)) :=
  if d.overflow == .shedOldest then
    if d.byPriority then
      match lowestClass d ws with
      | some c =>
        match takeFirst (fun r => r.cls == c) ws with
        | some x => some x
        | none => takeFirst (fun _ => true) ws
      | none => takeFirst (fun _ => true) ws
    else takeFirst (fun _ => true) ws
  else takeLast (fun _ => true) ws

theorem countP_true {β} (xs : List β) : xs.countP (fun _ => true) = xs.length := by
  simp

theorem chooseClass_some {κ α} (o : Overflow) (c : Nat) (ws : List (Req κ α)) r ys
    (h : chooseClass o c ws = some (r, ys)) :
    (r.cls == c) = true ∧ ∀ q, ys.countP q + (if q r then 1 else 0) = ws.countP q := by
  unfold chooseClass at h
  split at h
  · exact takeFirst_some _ _ _ _ h
  · exact takeLast_some _ _ _ _ h

theorem chooseAll_some {κ α} (d : ResourceDecl) (ws : List (Req κ α)) r ys
    (h : chooseAll d ws = some (r, ys)) :
    ∀ q, ys.countP q + (if q r then 1 else 0) = ws.countP q := by
  unfold chooseAll at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i heq; simp at h; subst h; exact (takeFirst_some _ _ _ _ heq).2
        · exact (takeFirst_some _ _ _ _ h).2
      · exact (takeFirst_some _ _ _ _ h).2
    · exact (takeFirst_some _ _ _ _ h).2
  · exact (takeLast_some _ _ _ _ h).2

theorem chooseAll_none {κ α} (d : ResourceDecl) (ws : List (Req κ α)) (h : chooseAll d ws = none) :
    ws.length = 0 := by
  rw [← countP_true]
  unfold chooseAll at h
  split at h
  · split at h
    · split at h
      · split at h
        · simp at h
        · exact takeFirst_none _ _ h
      · exact takeFirst_none _ _ h
    · exact takeFirst_none _ _ h
  · exact takeLast_none _ _ h

/-- The bounds step on a waiting list: each class bound in declaration order, then the resource
bound. Returns the remaining waiting list and the removed requests in order. -/
def boundClasses {κ α} (d : ResourceDecl) : List Nat → List (Req κ α) → List (Req κ α) → List (Req κ α) × List (Req κ α)
  | [], ws, removed => (ws, removed)
  | c :: cs, ws, removed =>
    match (d.classAt? c).bind (·.queueBound) with
    | none => boundClasses d cs ws removed
    | some b =>
      let (ws', rm) := enforce (fun ws => waitingC ws c) b (chooseClass d.overflow c) ws.length ws []
      boundClasses d cs ws' (removed ++ rm)

def boundAll {κ α} (d : ResourceDecl) (ws : List (Req κ α)) : List (Req κ α) × List (Req κ α) :=
  match d.queueBound with
  | none => (ws, [])
  | some b => enforce List.length b (chooseAll d) ws.length ws []

def bounds {κ α} (d : ResourceDecl) (ws : List (Req κ α)) : List (Req κ α) × List (Req κ α) :=
  let (ws1, rm1) := boundClasses d (List.range d.classes.length) ws []
  let (ws2, rm2) := boundAll d ws1
  (ws2, rm1 ++ rm2)

theorem enforce_class_bound {κ α} (o : Overflow) (c b : Nat) (ws : List (Req κ α)) :
    waitingC (enforce (fun ws => waitingC ws c) b (chooseClass o c) ws.length ws []).1 c ≤ b := by
  apply enforce_bound
  · intro xs h; unfold chooseClass at h; split at h
    · exact takeFirst_none _ _ h
    · exact takeLast_none _ _ h
  · intro xs r ys h
    obtain ⟨hp, hc⟩ := chooseClass_some o c xs r ys h
    have := hc (fun r => r.cls == c); simp [hp] at this; simp [waitingC]; omega
  · simp only [waitingC]; have := List.countP_le_length (p := fun r : Req κ α => r.cls == c) (l := ws); omega

theorem enforce_class_mono {κ α} (o : Overflow) (c b : Nat) (ws : List (Req κ α)) (q : Req κ α → Bool) :
    (enforce (fun ws => waitingC ws c) b (chooseClass o c) ws.length ws []).1.countP q ≤ ws.countP q := by
  apply enforce_mono (q := fun xs => xs.countP q)
  intro xs r ys h
  have := (chooseClass_some o c xs r ys h).2 q
  omega

theorem boundAll_mono {κ α} (d : ResourceDecl) (ws : List (Req κ α)) (q : Req κ α → Bool) :
    (boundAll d ws).1.countP q ≤ ws.countP q := by
  unfold boundAll
  split
  · exact Nat.le_refl _
  · apply enforce_mono (q := fun xs => xs.countP q)
    intro xs r ys h
    have := chooseAll_some d xs r ys h q
    omega

theorem boundAll_bound {κ α} (d : ResourceDecl) (ws : List (Req κ α)) (b : Nat)
    (hb : d.queueBound = some b) : (boundAll d ws).1.length ≤ b := by
  unfold boundAll
  rw [hb]
  apply enforce_bound
  · exact chooseAll_none d
  · intro xs r ys h
    have := chooseAll_some d xs r ys h (fun _ => true)
    simp only [countP_true] at this
    simp at this; omega
  · omega

theorem boundClasses_mono {κ α} (d : ResourceDecl) (q : Req κ α → Bool) :
    ∀ (cs : List Nat) (ws removed : List (Req κ α)),
      (boundClasses d cs ws removed).1.countP q ≤ ws.countP q := by
  intro cs
  induction cs with
  | nil => intro ws removed; simp [boundClasses]
  | cons c cs ih =>
    intro ws removed
    simp only [boundClasses]
    split
    · exact ih _ _
    · exact Nat.le_trans (ih _ _) (enforce_class_mono _ _ _ _ _)

theorem boundClasses_bound {κ α} (d : ResourceDecl) (c b : Nat)
    (hb : (d.classAt? c).bind (·.queueBound) = some b) :
    ∀ (cs : List Nat) (ws removed : List (Req κ α)), c ∈ cs →
      waitingC (boundClasses d cs ws removed).1 c ≤ b := by
  intro cs
  induction cs with
  | nil => intro _ _ h; simp at h
  | cons c' cs ih =>
    intro ws removed hmem
    simp only [boundClasses]
    by_cases hc : c' = c
    · subst hc
      rw [hb]
      simp only
      exact Nat.le_trans (boundClasses_mono d _ cs _ _) (enforce_class_bound _ _ _ _)
    · have hmem' : c ∈ cs := by
        cases hmem with
        | head => exact absurd rfl hc
        | tail _ h => exact h
      split
      · exact ih _ _ hmem'
      · exact ih _ _ hmem'

/-- **Queue bounds.** After the bounds step every class with a `queueBound` has at most that many
waiting requests, and the waiting list is within the resource's `queueBound`. -/
theorem bounds_ok {κ α} (d : ResourceDecl) (ws : List (Req κ α)) :
    (∀ c b, c < d.classes.length → (d.classAt? c).bind (·.queueBound) = some b →
      waitingC (bounds d ws).1 c ≤ b) ∧
    (∀ b, d.queueBound = some b → (bounds d ws).1.length ≤ b) := by
  refine ⟨fun c b hc hb => ?_, fun b hb => ?_⟩
  · simp only [bounds, waitingC]
    exact Nat.le_trans (boundAll_mono d _ _)
      (boundClasses_bound d c b hb _ ws [] (List.mem_range.mpr hc))
  · exact boundAll_bound d _ b hb

/-! ## Axioms

No `sorry` and no axiom of our own: these pins fail the build otherwise. -/

/-- info: 'Exegra.Res.bounds_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bounds_ok

/-- info: 'Exegra.Res.grantLoop_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grantLoop_ok

/-- info: 'Exegra.Res.consume_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms consume_ok

/-- info: 'Exegra.Res.endService_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms endService_ok

end Exegra.Res
