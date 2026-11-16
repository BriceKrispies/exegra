import Exegra.Semantics

/-
Properties of the semantics, proved with no `sorry`, no `admit` and no axiom of our own. The
`#guard_msgs` checks at the end make `lake build` fail if any theorem here comes to depend on
`sorryAx` or on an axiom other than Lean's standard ones.

1. Determinism. `step` and `runText` are functions, so equal inputs give equal results by
   construction; the theorems state it.
2. At most one fired transition per behavior: in every step, the behaviors of the fired
   transitions are a sublist of the run's behaviors (in scenario order, each entry at most
   once); when behavior ids are distinct, no behavior fires twice in a step.
3. Termination within the step limit: every run stops (its outcome is not `running`) after at
   most `stepBound stepLimit` steps. The fuel of `loop` never runs out first.
4. Faults: a `drop` step fires nothing and records only `dropped` faults, at least one; and a
   failed step keeps nothing (its configuration is the one before it, and it records nothing).
-/

namespace Exegra

/-! ## 1. Determinism -/

/-- The step function is a function: one configuration has exactly one step result. -/
theorem step_deterministic (env : Env) (c : Config) (r₁ r₂ : StepResult)
    (h₁ : step env c = r₁) (h₂ : step env c = r₂) : r₁ = r₂ :=
  h₁.symm.trans h₂

/-- Two runs from the same engine input give the same trace (or the same refusal). -/
theorem runInput_deterministic (i₁ i₂ : SimInput) (h : i₁ = i₂) : runInput i₁ = runInput i₂ :=
  h ▸ rfl

/-- Two runs from the same input text give the same trace text (or the same refusal). -/
theorem runText_deterministic (t : String) (o₁ o₂ : Except String String)
    (h₁ : runText t = o₁) (h₂ : runText t = o₂) : o₁ = o₂ :=
  h₁.symm.trans h₂

/-! ## 2. At most one fired transition per behavior -/

theorem fireOne_behavior {input : SimInput} {bid : String} {t : TransitionIn} {payload : Value}
    {time : Float} {s : FireState} {f : Fired} {s' : FireState}
    (h : fireOne input bid t payload time s = .ok (f, s')) : f.behavior = bid := by
  unfold fireOne at h
  split at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

theorem fireAll_behaviors {input : SimInput} {payload : Value} {time : Float} :
    ∀ (ws : List (String × TransitionIn)) (s : FireState) (fs : List Fired) (s' : FireState),
      fireAll input payload time ws s = .ok (fs, s') → fs.map (·.behavior) = ws.map (·.1)
  | [], s, fs, s', h => by
    simp only [fireAll, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | (bid, t) :: ws, s, fs, s', h => by
    simp only [fireAll] at h
    split at h
    · cases h
    · rename_i f s1 h1
      split at h
      · cases h
      · rename_i fs1 s2 h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp [fireOne_behavior h1, fireAll_behaviors ws s1 fs1 s2 h2]

theorem choose_winners {faults : List FaultIn} {cur : Configuration} {event : String}
    {payload : Value} {time : Float} :
    ∀ (bs : List (String × List TransitionIn)) (ws : List (String × TransitionIn))
      (igs : List Ignored) (fs : List FaultRecord),
      choose faults cur event payload time bs = .ok (ws, igs, fs) →
      (ws.map (·.1)).Sublist (bs.map (·.1))
  | [], ws, igs, fs, h => by
    simp only [choose, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Sublist.refl _
  | (bid, ts) :: bs, ws, igs, fs, h => by
    simp only [choose] at h
    split at h
    · cases h
    · rename_i c recs _
      split at h
      · cases h
      · rename_i ws1 igs1 fs1 h2
        have ih := choose_winners bs ws1 igs1 fs1 h2
        cases c with
        | win t =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact List.Sublist.cons_cons _ ih
        | ignore i =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact List.Sublist.cons _ ih

theorem deliver_fired {env : Env} {cur : Configuration} {head : Pending} {s : FireState}
    {fired : List Fired} {igs : List Ignored} {recs : List FaultRecord} {s' : FireState}
    (h : deliver env cur head s = .ok (fired, igs, recs, s')) :
    (fired.map (·.behavior)).Sublist (env.behaviors.map (·.1)) := by
  unfold deliver at h
  split at h
  · cases h
  · rename_i ws igs1 recs1 h1
    split at h
    · cases h
    · rename_i fired1 s1 h2
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [fireAll_behaviors ws s fired1 s1 h2]
      exact choose_winners env.behaviors ws igs1 recs1 h1

/-- In a committed step handled from the queue head, the fired transitions' behaviors form a
sublist of the run's behaviors. -/
theorem stepHead_fired {env : Env} {c : Config} {next : Configuration} {nid : Nat}
    {head : Pending} {rec : Step} {c' : Config}
    (h : stepHead env c next nid head = .committed rec c') :
    (rec.fired.map (·.behavior)).Sublist (env.behaviors.map (·.1)) := by
  unfold stepHead at h
  cases hd : dropsOf env c head with
  | cons d ds =>
    simp only [hd, StepResult.committed.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [blankStep]
  | nil =>
    simp only [hd] at h
    cases hy : delayOf? env c head with
    | some d =>
      simp only [hy, StepResult.committed.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [blankStep]
    | none =>
      simp only [hy] at h
      cases hv : deliver env c.conf head { next := next, seq := c.seq, nid := nid } with
      | error msg => simp only [hv] at h; cases h
      | ok r =>
        obtain ⟨fired, igs, recs, s⟩ := r
        simp only [hv, StepResult.committed.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact deliver_fired hv

/-- **At most one fired transition per behavior entry.** In every committed step, the
behaviors of the fired transitions are a sublist of the run's behaviors in scenario order. -/
theorem step_fired_sublist {env : Env} {c : Config} {rec : Step} {c' : Config}
    (h : step env c = .committed rec c') :
    (rec.fired.map (·.behavior)).Sublist (env.behaviors.map (·.1)) := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact stepHead_fired h

/-- **At most one fired transition per behavior.** When behavior ids are distinct, no behavior
fires twice in a committed step. -/
theorem step_fired_nodup {env : Env} {c : Config} {rec : Step} {c' : Config}
    (h : step env c = .committed rec c') (hnd : (env.behaviors.map (·.1)).Nodup) :
    (rec.fired.map (·.behavior)).Nodup :=
  List.Nodup.sublist (step_fired_sublist h) hnd

/-! ## 4. Faults and failed steps (used below for whole runs) -/

theorem stepHead_failed {env : Env} {c : Config} {next : Configuration} {nid : Nat}
    {head : Pending} {rec : Step} (h : stepHead env c next nid head = .failed rec) :
    rec.config = c.conf ∧ rec.kind = .deliver ∧ rec.fired = [] ∧ rec.ignored = [] ∧
      rec.faults = [] ∧ rec.error.isSome := by
  unfold stepHead at h
  cases hd : dropsOf env c head with
  | cons d ds => simp only [hd] at h; cases h
  | nil =>
    simp only [hd] at h
    cases hy : delayOf? env c head with
    | some d => simp only [hy] at h; cases h
    | none =>
      simp only [hy] at h
      cases hv : deliver env c.conf head { next := next, seq := c.seq, nid := nid } with
      | ok r => obtain ⟨fired, igs, recs, s⟩ := r; simp only [hv] at h; cases h
      | error msg =>
        simp only [hv, StepResult.failed.injEq] at h
        subst h
        simp [blankStep]

/-- **A failed step keeps nothing.** Its configuration is the one before the step, it fires,
ignores and records nothing, and it carries an error. -/
theorem step_failed {env : Env} {c : Config} {rec : Step} (h : step env c = .failed rec) :
    rec.config = c.conf ∧ rec.kind = .deliver ∧ rec.fired = [] ∧ rec.ignored = [] ∧
      rec.faults = [] ∧ rec.error.isSome := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact stepHead_failed h

theorem stepHead_drop {env : Env} {c : Config} {next : Configuration} {nid : Nat}
    {head : Pending} {rec : Step} {c' : Config}
    (h : stepHead env c next nid head = .committed rec c') (hk : rec.kind = .drop) :
    rec.fired = [] ∧ rec.faults ≠ [] ∧ ∀ f ∈ rec.faults, f.effect = .dropped := by
  unfold stepHead at h
  cases hd : dropsOf env c head with
  | cons d ds =>
    simp only [hd, StepResult.committed.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨rfl, by simp, ?_⟩
    intro f hf
    simp only [List.mem_map] at hf
    obtain ⟨_, _, rfl⟩ := hf
    rfl
  | nil =>
    simp only [hd] at h
    cases hy : delayOf? env c head with
    | some d =>
      simp only [hy, StepResult.committed.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [blankStep] at hk
    | none =>
      simp only [hy] at h
      cases hv : deliver env c.conf head { next := next, seq := c.seq, nid := nid } with
      | error msg => simp only [hv] at h; cases h
      | ok r =>
        obtain ⟨fired, igs, recs, s⟩ := r
        simp only [hv, StepResult.committed.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp [blankStep] at hk

/-- **A dropped event fires no transition.** A committed `drop` step fires nothing, and its
fault records are all `dropped` (at least one). -/
theorem step_drop {env : Env} {c : Config} {rec : Step} {c' : Config}
    (h : step env c = .committed rec c') (hk : rec.kind = .drop) :
    rec.fired = [] ∧ rec.faults ≠ [] ∧ ∀ f ∈ rec.faults, f.effect = .dropped := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact stepHead_drop h hk

/-! ## Runs -/

theorem loop_not_running {env : Env} {bound : Nat} :
    ∀ (n : Nat) (r : Run), r.outcome ≠ .running → loop env bound n r = r
  | 0, _, _ => rfl
  | _ + 1, r, h => by simp [loop, h]

/-- Every step a run records satisfies any property that every committed and every failed
step satisfies. -/
theorem loop_steps {env : Env} {bound : Nat} (P : Step → Prop)
    (hc : ∀ c rec c', step env c = .committed rec c' → P rec)
    (hf : ∀ c rec, step env c = .failed rec → P rec) :
    ∀ (n : Nat) (r : Run), (∀ s ∈ r.stepsRev, P s) → ∀ s ∈ (loop env bound n r).stepsRev, P s
  | 0, r, h => h
  | n + 1, r, h => by
    simp only [loop]
    split
    · apply loop_steps P hc hf n
      intro s hs
      cases heq : step env r.config with
      | idle =>
        simp only [advance, heq] at hs
        exact h s hs
      | committed rec next =>
        simp only [advance, heq, List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hc _ _ _ heq
        · exact h s hs
      | failed rec =>
        simp only [advance, heq, List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hf _ _ heq
        · exact h s hs
    · exact h

theorem advance_length_le (env : Env) (bound : Nat) (r : Run) :
    (advance env bound r).stepsRev.length ≤ r.stepsRev.length + 1 := by
  cases hs : step env r.config with
  | idle => simp [advance, hs]
  | committed rec next => simp [advance, hs]
  | failed rec => simp [advance, hs]

theorem advance_running (env : Env) (bound : Nat) (r : Run)
    (h : (advance env bound r).outcome = .running) :
    (advance env bound r).stepsRev.length = r.stepsRev.length + 1 ∧
      r.stepsRev.length + 1 < bound := by
  cases hs : step env r.config with
  | idle => simp [advance, hs] at h
  | failed rec => simp [advance, hs] at h
  | committed rec next =>
    simp only [advance, hs] at h ⊢
    refine ⟨by simp, ?_⟩
    by_cases he : next.conf.pending.isEmpty = true
    · simp [he] at h
    · by_cases hb : r.stepsRev.length + 1 ≥ bound
      · simp [he, hb] at h
      · omega

theorem loop_spec (env : Env) (bound : Nat) :
    ∀ (n : Nat) (r : Run),
      (r.outcome = .running → r.stepsRev.length < bound) →
      bound ≤ r.stepsRev.length + n →
      r.stepsRev.length ≤ bound →
      (loop env bound n r).outcome ≠ .running ∧ (loop env bound n r).stepsRev.length ≤ bound
  | 0, r, hinv, hn, hle => by
    refine ⟨?_, hle⟩
    intro hr
    have := hinv hr
    simp only [loop] at hr ⊢
    omega
  | n + 1, r, hinv, hn, hle => by
    by_cases hr : r.outcome = .running
    · simp only [loop, hr, ite_true]
      have hlt := hinv hr
      by_cases hr' : (advance env bound r).outcome = .running
      · obtain ⟨hlen, hb⟩ := advance_running env bound r hr'
        apply loop_spec env bound n
        · intro _; omega
        · omega
        · omega
      · rw [loop_not_running n _ hr']
        have := advance_length_le env bound r
        exact ⟨hr', by omega⟩
    · simp only [loop, hr, ite_false]
      exact ⟨hr, hle⟩

/-- **Every run stops within the step bound.** With fuel equal to the bound, the run is no longer
`running` when the loop ends, and it has taken at most `bound` steps. -/
theorem run_stops (env : Env) (bound : Nat) (c0 : Config) (hb : 0 < bound) :
    (runEnv env bound c0).outcome ≠ .running ∧ (runEnv env bound c0).stepsRev.length ≤ bound := by
  apply loop_spec env bound bound (startRun c0)
  · intro _; simp [startRun]; exact hb
  · simp [startRun]
  · simp [startRun]

theorem stepBound_pos (limit : Float) : 0 < stepBound limit := by
  unfold stepBound
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem runInput_ok {i : SimInput} {tr : Trace} (h : runInput i = .ok tr) : tr = traceOf i := by
  unfold runInput at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h
    exact h.symm

/-! ## The properties for whole runs of an engine input -/

/-- **Termination under the step limit.** Every run of an engine input stops (its outcome is
`quiescent`, `step-limit` or `error`, never `running`) after at most `stepBound stepLimit`
steps: `max 1 ⌈stepLimit⌉`. -/
theorem runInput_terminates {i : SimInput} {tr : Trace} (h : runInput i = .ok tr) :
    tr.outcome ≠ .running ∧ tr.steps.length ≤ stepBound i.scenario.stepLimit := by
  have hok := runInput_ok h
  subst hok
  have := run_stops (envOf i) (stepBound i.scenario.stepLimit) (initialConfig i).2
    (stepBound_pos _)
  simpa [traceOf] using this

theorem envOf_behaviorIds (i : SimInput) :
    (envOf i).behaviors.map (·.1) = i.behaviors.map (·.id) := by
  simp [envOf, List.map_map, Function.comp_def]

/-- **At most one fired transition per behavior, for every step of a run.** In every step of
the trace, the fired transitions' behaviors are a sublist of the input's behaviors. -/
theorem runInput_fired_sublist {i : SimInput} {tr : Trace} (h : runInput i = .ok tr) :
    ∀ st ∈ tr.steps, (st.fired.map (·.behavior)).Sublist (i.behaviors.map (·.id)) := by
  have hok := runInput_ok h
  subst hok
  intro st hst
  simp only [traceOf, List.mem_reverse] at hst
  rw [← envOf_behaviorIds]
  refine loop_steps (fun st => (st.fired.map (·.behavior)).Sublist
      ((envOf i).behaviors.map (·.1))) ?_ ?_ _ _ ?_ st hst
  · intro c rec c' hc
    exact step_fired_sublist hc
  · intro c rec hf
    simp [(step_failed hf).2.2.1]
  · simp [startRun]

/-- **No behavior fires twice in a step**, for every step of a run of an input whose behavior
ids are distinct (as in every input derived from a validated model). -/
theorem runInput_fired_unique {i : SimInput} {tr : Trace}
    (hnd : (i.behaviors.map (·.id)).Nodup) (h : runInput i = .ok tr) :
    ∀ st ∈ tr.steps, (st.fired.map (·.behavior)).Nodup :=
  fun st hst => List.Nodup.sublist (runInput_fired_sublist h st hst) hnd

/-- **A dropped event fires no transition**, in every step of a run: a `drop` step fires
nothing and records only `dropped` faults, at least one. -/
theorem runInput_drop {i : SimInput} {tr : Trace} (h : runInput i = .ok tr) :
    ∀ st ∈ tr.steps, st.kind = .drop →
      st.fired = [] ∧ st.faults ≠ [] ∧ ∀ f ∈ st.faults, f.effect = .dropped := by
  have hok := runInput_ok h
  subst hok
  intro st hst
  simp only [traceOf, List.mem_reverse] at hst
  refine loop_steps (fun st => st.kind = .drop →
      st.fired = [] ∧ st.faults ≠ [] ∧ ∀ f ∈ st.faults, f.effect = .dropped) ?_ ?_ _ _ ?_ st hst
  · intro c rec c' hc hk
    exact step_drop hc hk
  · intro c rec hf hk
    rw [(step_failed hf).2.1] at hk
    cases hk
  · simp [startRun]

/-! ## Axiom check

Each theorem depends only on Lean's standard axioms; `sorryAx` or an axiom of our own would
change these messages and fail the build. -/

/-- info: 'Exegra.step_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_deterministic

/-- info: 'Exegra.runInput_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runInput_deterministic

/-- info: 'Exegra.runText_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runText_deterministic

/-- info: 'Exegra.step_fired_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_fired_sublist

/-- info: 'Exegra.step_fired_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_fired_nodup

/-- info: 'Exegra.runInput_fired_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runInput_fired_sublist

/-- info: 'Exegra.runInput_fired_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runInput_fired_unique

/-- info: 'Exegra.run_stops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_stops

/-- info: 'Exegra.runInput_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runInput_terminates

/-- info: 'Exegra.step_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_drop

/-- info: 'Exegra.runInput_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runInput_drop

/-- info: 'Exegra.step_failed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_failed

end Exegra
