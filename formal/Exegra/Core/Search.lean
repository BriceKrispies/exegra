import Exegra.Core.LTS
import Exegra.Search

/-
The bridge from the generic search of `Exegra.Search` to the transition systems of
`Exegra.Core.LTS` (docs/foundations.md, M1; used by M4).

`Gen.search` is proved about its own successor function (`Gen.Sys.next`). These theorems say when
its results are results about an `LTS`:

* `Covers S M`: every initial state of `M` is an initial node of `S`, and every step of `M` is a
  successor in `S`. Then a `holds` result proves `M.Invariant` with no bound (`invariant_of_search`).
  This is the direction an explorer's completeness obligation discharges; without it a `holds` says
  nothing about `M`.
* `Sound S M`: every initial node of `S` is initial in `M`, and every successor in `S` is a step of
  `M`. Then a `counterexample` result refutes `M.Invariant` (`not_invariant_of_search`).
* `Enum.toSys` turns a complete enumeration into a search system that covers and is sound for `M`.
-/

namespace Exegra.Core.LTS

variable {σ α : Type}

/-- Every initial state and every step of `M` is present in `S`. -/
structure Covers (S : Gen.Sys σ) (M : LTS σ α) : Prop where
  init : ∀ s, M.init s → s ∈ S.init
  step : ∀ s a t, M.step s a t → ∃ k, S.next s k = some t

/-- Every initial node and every successor of `S` is present in `M`. -/
structure Sound (S : Gen.Sys σ) (M : LTS σ α) : Prop where
  init : ∀ s, s ∈ S.init → M.init s
  step : ∀ s k t, S.next s k = some t → ∃ a, M.step s a t

theorem gen_reach_of_reach {S : Gen.Sys σ} {M : LTS σ α} (hc : Covers S M) {s : σ}
    (h : M.Reach s) : ∃ d, Gen.Reach S d s := by
  induction h with
  | init hi => exact ⟨0, .init (hc.init _ hi)⟩
  | step _ hst ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨k, hk⟩ := hc.step _ _ _ hst
    exact ⟨d + 1, .step hd ⟨k, Gen.mem_succs.mpr hk⟩⟩

theorem reach_of_gen_reach {S : Gen.Sys σ} {M : LTS σ α} (hs : Sound S M) {d : Nat} {s : σ}
    (h : Gen.Reach S d s) : M.Reach s := by
  induction h with
  | init hi => exact .init (hs.init _ hi)
  | step _ hk ih =>
    obtain ⟨k, hk⟩ := hk
    obtain ⟨a, ha⟩ := hs.step _ _ _ (Gen.mem_succs.mp hk)
    exact .step ih ha

variable [DecidableEq σ] [Hashable σ]

/-- **A `holds` result of the search proves an unbounded invariant** of every system it covers. -/
theorem invariant_of_search {S : Gen.Sys σ} {M : LTS σ α} (hc : Covers S M) {ok : σ → Bool}
    {bound cap n : Nat} (h : Gen.search S ok bound cap = .holds n) :
    M.Invariant (fun s => ok s = true) := by
  intro s hs
  obtain ⟨d, hd⟩ := gen_reach_of_reach hc hs
  exact Gen.search_sound h d s hd

/-- **A counterexample of the search refutes the invariant** of every system it is sound for. -/
theorem not_invariant_of_search {S : Gen.Sys σ} {M : LTS σ α} (hs : Sound S M) {ok : σ → Bool}
    {bound cap : Nat} {p : Gen.Path σ} (h : Gen.search S ok bound cap = .counterexample p) :
    ¬ M.Invariant (fun s => ok s = true) := by
  intro hinv
  obtain ⟨hr, -, t, ht, hok⟩ := Gen.search_counterexample_real h
  obtain ⟨d, hd⟩ := Gen.greplay_reach_any hr ht
  have := hinv t (reach_of_gen_reach hs hd)
  rw [hok] at this
  exact Bool.false_ne_true this

/-- The search system of a complete enumeration. -/
def Enum.toSys {M : LTS σ α} (E : Enum M) : Gen.Sys σ where
  init := E.inits
  width s := (E.succ s).length
  next s k := (E.succ s)[k]?
  lt := by
    intro s k t h
    exact (List.getElem?_eq_some_iff.mp h).1

theorem Enum.toSys_covers {M : LTS σ α} (E : Enum M) : Covers E.toSys M where
  init := E.init_complete
  step := by
    intro s a t h
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem (E.succ_complete s a t h)
    exact ⟨k, by simp [Enum.toSys, List.getElem?_eq_getElem hk, he]⟩

end Exegra.Core.LTS
