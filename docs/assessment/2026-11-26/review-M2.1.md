# Adversarial review of M2.1 (instantaneous behaviour calculus)

Reviewed: commit 82fbd5c, `formal/Exegra/Core/Behav.lean`, `formal/Exegra/Core/BehavExamples.lean`, the
five `behav-*` claims and the `lts-foundation` component of `specs/exegra/spec.jsonc`, against
docs/foundations.md (sections 3-4, M1, M2), plan-M2.md (M2.1, section 2.2) and review-M1.md.

Demonstrations: `scripts/review-M2.1-demo.lean`,
compiled with `lake env lean` from `formal/` (Lean 4.35.0). It compiles with no error; every `example` below is
checked by `decide`, and the `#eval` output is quoted verbatim.

All proofs in the commit are correct as written (`lake env lean` on the demo re-elaborates both files'
dependencies). The findings concern what they claim, what is missing, and fidelity to format 2.

## Summary

| # | Finding | Severity |
|---|---------|----------|
| 1 | The step is not order-independent: winner order changes the pending queue and so the state (D1). `phase2_perm` covers machines only; the docstring's "this is what lets the relation fire winners in machine order without quantifying over orders" does not follow | MUST-FIX |
| 2 | `%` is `Int.emod`; format 2 is truncated remainder. Typed integer `/` truncates in format 2, is `inexact` here (D2) | MUST-FIX |
| 3 | Overflow is checked against ±2^53 on every operation and against the declared sort only at `set`; format 2 checks the declared integer type on every operation (D3). The header's "an integer outside the range of its sort is `overflow`" overclaims | MUST-FIX |
| 4 | `winners` is Nodup but no theorem says so; `phase2_perm` is never connected to `deliver` | SHOULD-FIX |
| 5 | `phase2_eq_par` (the plan's lemma, the parallel closed form) was not delivered | SHOULD-FIX |
| 6 | `Expr.ty?` is unsound for `eval`: literals, payload fields, time (D4) | SHOULD-FIX |
| 7 | `f4_next_reads_differ` is about `afterNext`, not the rule; `phase2Next` is a re-implementation with known divergences from Format2.lean; the claim's prose says "today's interpreters" | SHOULD-FIX |
| 8 | Pending is appended; format 2 inserts time-sorted (D6). `step_sound` (M2.3) needs either the same insertion or a Perm abstraction, so `pending_perm_bisim` is not optional | SHOULD-FIX |
| 9 | `Err.shape` is reachable from an ill-shaped `init` (D5); no shape-preservation theorem, no `Sys.WF` | SHOULD-FIX |
| 10 | The f4 invariants are meaningful but per-example; "one verdict" in general needs a renaming theorem | NOTE |
| 11 | Labels are positions: unusable for per-entry fairness (M5) | NOTE |
| 12 | Smaller fidelity gaps (`==` across sorts, string `+`, `>`/`>=`, operand order, error identity, no targets) | NOTE |
| 13 | M6: closed systems with dependent `Fin` scoping | NOTE |

## 1. Emission order: the step is not order-independent (MUST-FIX)

`phase2_perm` concludes `toOption.map Prod.fst` equality, i.e. machines only. `phase2_perm_emitted`
gives a `Perm` of emitted entries. `deliverWith` appends them: `pending := c0.pending ++ out`
(Behav.lean:480). The state is `.run c` with `c.pending : List Entry`, so two winner orders give
**different states**, and any state predicate (and the index labels) can tell them apart.

Demo D1 (`emSys`: two machines, on event 0 machine m emits event m+1 after 0):

```
#eval (phase2 emSys c0 e0 [w0, w1] c0.machines).toOption.map Prod.snd
some [{ time := 0, event := 1, payload := [] }, { time := 0, event := 2, payload := [] }]
#eval (phase2 emSys c0 e0 [w1, w0] c0.machines).toOption.map Prod.snd
some [{ time := 0, event := 2, payload := [] }, { time := 0, event := 1, payload := [] }]
```
and, checked by `decide`, with `deliverRev` = `deliverWith sys (fun c e ws ms => phase2 sys c e ws.reverse ms)`:
```lean
example : (deliver emSys emSys.init 0).map (·.toOption) ≠ (deliverRev emSys emSys.init 0).map (·.toOption)
example : ((deliver emSys emSys.init 0).bind (·.toOption)).map (fun c => (c.pending[0]?).map (·.event)) = some (some 1)
example : ((deliverRev emSys emSys.init 0).bind (·.toOption)).map (fun c => (c.pending[0]?).map (·.event)) = some (some 2)
```
Downstream: the next step's label 0 delivers event 1 in one order and event 2 in the other. The *sets*
of successors agree up to queue permutation (because any minimal-time entry may be delivered), but that
is exactly `pending_perm_bisim`, which the plan calls optional (plan 2.2, "optional theorem, M2.3").
Without it, "the relation need not quantify over orders" is unproved, and the one-verdict criterion
holds only for predicates that are invariant under pending permutation — which nothing states.

Fix. Define the equivalence and prove the step-level statement now (machines equal, pending Perm), and
make `pending_perm_bisim` mandatory in M2.3:
```lean
def Cfg.Equiv (c d : Cfg) : Prop := c.time = d.time ∧ c.machines = d.machines ∧ c.pending.Perm d.pending
theorem deliverWith_perm {sys : Sys} {c : Cfg} {k : Nat}
    (σ : ∀ c e, List (Winner sys) → List (Winner sys)) (hσ : ∀ c e ws, (σ c e ws).Perm ws) :
    Option.Rel (fun r r' => match r, r' with
      | .ok a, .ok b => a.Equiv b | .error _, .error _ => True | _, _ => False)
      (deliver sys c k) (deliverWith sys (fun c e ws ms => phase2 sys c e (σ c e ws) ms) c k)
theorem pending_perm_bisim (sys : Sys) :
    (Sys.lts sys).Bisim (fun s t => match s, t with
      | .run c, .run d => c.Equiv d | .err c, .err d => c.Equiv d | _, _ => False)
```
(`Bisim` labels differ by the index permutation; state it with an existential over labels, or label
by entry — see 11.) Also restate the Behav.lean header bullet and the `phase2_perm` docstring.

## 2. `%` and integer `/` differ from format 2 (MUST-FIX)

`BOp.apply .mod` uses Lean's `Int` `%` = `Int.emod` (Behav.lean:271). Format 2 uses `Num.fmod`
(truncated, sign of the dividend; Expr.lean:364) for both untyped and typed `%`. Typed integer `/`
truncates toward zero in format 2 (`divIn`, Expr.lean:301-304); here a remainder is `Err.inexact`
(Behav.lean:270). Demo D2:
```
#eval BOp.apply .mod (.int (-7)) (.int 2)                       Except.ok (Val.int 1)
format 2, untyped "(0 - 7) % 2"                                 "ok -1"
format 2, x : i32 = -7, "x % 2"                                 "ok -1"
format 2, x : i32 = 7,  "x / 2"                                 "ok 3"
#eval BOp.apply .div (.int 7) (.int 2)                          Except.error Err.inexact
```
The `%` case is a silently different *value*, not an error: M2.4's elaborated program and M2.3's
`step_sound` would disagree on negative operands without any error flag. The `/` case makes every
typed integer division with a remainder fail in the calculus where format 2 succeeds.

Fix:
```lean
| .mod, .int a, .int b => if b = 0 then .error .divZero else intRes (a.tmod b)
| .tdiv, .int a, .int b => if b = 0 then .error .divZero else intRes (a.tdiv b)  -- typed int `/`
| .div,  .int a, .int b => ...  -- untyped `/`: exact or `inexact`, as now
```
with `theorem mod_tmod : BOp.apply .mod (.int (-7)) (.int 2) = .ok (.int (-1))`-style pins.

## 3. Overflow is not relative to declared integer types (MUST-FIX)

`intRes` (Behav.lean:255) checks ±`maxSafe` only; the declared range is checked only by `Val.check` at
`set` (Behav.lean:367). `BOp.ty?` returns `.num` for arithmetic, discarding operand ranges
(Behav.lean:200). Format 2's `intResult` checks operands and result against the declared `IntKind`
on every operator, unary minus included (Expr.lean:289-296, 323-324). Demo D3, `x : u8 = 200`,
guard `x + 100 > 255`:
```
format 2:   "error: Integer overflow: \"+\" on u8 gives 300, outside 0..255"
calculus:   Except.ok (Val.bool true)        -- and `decide` checks it
```
So a format-2 `.failed` step corresponds to a calculus `.run` step: `step_sound` is false on the
typed-integer fragment, and the header sentence "an integer outside the range of its sort is the error
`overflow`" claims more than holds (it holds for writes, not for intermediate values, guards or payloads).

Fix: carry the operator's integer sort in the syntax (the elaborator fills it from format 2's
`staticTy`) and check it in `apply`, mirroring `intResult`:
```lean
| arith (op : AOp) (τ : Ty) (a b : Expr S me)       -- replaces add/sub/mul/div/mod in BOp
def AOp.apply (τ : Ty) (op : AOp) : Val → Val → Except Err Val
  | .int a, .int b => do let _ ← Val.check τ (.int a); let _ ← Val.check τ (.int b); ... Val.check τ (.int r)
```
with `Ty.num` for untyped arithmetic (whose 2^53 limit stays as now).

## 4. Winners are Nodup, but nothing says so (SHOULD-FIX)

`phase2_perm` takes `hnd : (ws.map (·.mach)).Nodup`; nothing proves that the list `deliver` computes
satisfies it, so `phase2_perm` is never instantiated at a real step. It is true and short; the demo
proves it (axioms `[propext, Quot.sound]`):
```lean
theorem finList_nodup (n : Nat) : (finList n).Nodup
theorem winnersOf_sublist {sys c e} (ms : List (Fin sys.sig.machines)) (ws : List (Winner sys)) :
    winnersOf sys c e ms = .ok ws → (ws.map (·.mach)).Sublist ms
theorem winners_nodup {sys : Sys} {c : Cfg} {e : Entry} {ws : List (Winner sys)}
    (h : winners sys c e = .ok ws) : (ws.map (·.mach)).Nodup
```
Add these and a corollary at the step: `deliverWith_perm` (finding 1) uses `winners_nodup`.

## 5. `phase2_eq_par` is missing (SHOULD-FIX)

The plan names it as the lemma `phase2_perm` rests on; the commit proves `phase2_perm` by a swap
lemma instead. The closed form is what M2.3 (`step_sound`: relate a sequential executable to the
relation) and M6 (a product step is a parallel update) need:
```lean
theorem phase2_eq_par {sys c e} {ws : List (Winner sys)} (hnd : (ws.map (·.mach)).Nodup) :
    machinesAfter (phase2 sys c e ws c.machines) =
      (ws.mapM (fun w => (c.machines[w.mach.val]?).bind fun o => (fireOne sys c e w o).toOption
        |>.map (w.mach.val, ·.1))).map (fun upd => upd.foldl (fun ms (i, s) => ms.set i s) c.machines)
```

## 6. `Expr.ty?` is unsound for `eval` (SHOULD-FIX)

No theorem rests on `ty?` yet, but its shape blocks the M2.2 `Sys.WF` theorems. Demo D4, by `decide`:
```lean
example : big.ty? = some Ty.num ∧ (big.eval cx).toOption.map (·.fits Ty.num) = some false   -- .val (.int (2^60))
example : fld.ty? = some (.int 0 255) ∧ (fld.eval cx').toOption.map (·.fits (.int 0 255)) = some false
          -- .field 7 (.int 0 255) with payload [(7, .int 1000)]: `Ref.eval` checks only `sameSort`
```
and `.time` is typed `.int 0 maxSafe` while `Cfg.time : Nat` is unbounded (no `timeBound` until M2.2).
Fix: `Val.ty (.int v) := .int v v`; `Ref.eval (.field f τ)` uses `Val.check τ`; state the target
`theorem eval_fits (h : e.ty? = some τ) (hwf : cx.WF) : ∀ v, e.eval cx = .ok v → v.fits τ`.

## 7. `f4_next_reads_differ` is about the example, not the rule (SHOULD-FIX)

The statement mentions `afterNext`, `yAB`, `yBA`, `f4AB`, `f4BA`; `deliverNext` and `phase2Next` are
not in it, and the lean-theorem checker refuses an `about` constant not in the statement
(tools/lean-theorems.js:73-77, claims.js:477), so the claim cannot name the rule it is about.
`phase2Next` (Behav.lean:407) is a re-implementation, linked to `Exegra.V2` by no theorem or test.
For this example it matches Format2.lean (`fireAll` 1559-1565 in scenario order; `runEffects` evaluates
against `s.next`, 1415; `resolve` reads `[b, name]` from `view`, 1167-1176), but it differs in general:
an absent variable resolves to `.undef` in format 2 (1148, 1176) and to `Err.shape` here; aggregates and
resources are absent; emitted entries are inserted sorted in format 2. The claim's prose "the
next-configuration rule of today's interpreters" is stronger than the theorem; the rationale's hedge
is correct but the statement should carry it. Fix:
```lean
theorem f4_next_reads_differ :
    (deliverNext f4AB f4Init 0).map (outcome f4Init) = some (.run ⟨0, [⟨0, [.int 1]⟩, ⟨0, [.int 1]⟩], []⟩) ∧
    (deliverNext f4BA f4Init 0).map (outcome f4Init) = some (.run f4BA1)
```
with `about: [Exegra.Core.Behav.deliverNext, ...f4AB, ...f4BA]` and prose "in the calculus's model
(`deliverNext`) of today's rule". A differential `#eval` of `Exegra.V2` on the format-2 fixture of the
example belongs in M2.5 and should be listed there.

## 8. Queue insertion differs from format 2 (SHOULD-FIX)

Format 2 inserts emitted entries time-sorted and stable (`insertE`, Format2.lean:1022-1025) and always
delivers index 0 (`step`, 2313-2321). The calculus appends. Demo D6 (pending `[t=0, t=10]`, the step
emits at +5):
```
#eval ((deliver oSys oSys.init 0).bind (·.toOption)).map (fun c => c.pending.map (·.time))
some [10, 5]          -- format 2: [5, 10]
```
So no abstraction *function* from format-2 configurations to calculus states commutes with the step;
`step_sound` must be modulo Perm (finding 1) or the calculus must insert like format 2. Recommended:
```lean
def insertByTime (q : List Entry) (e : Entry) : List Entry   -- = insertE on (time) keys, stable
-- in deliverWith: pending := out.foldl insertByTime c0.pending
theorem insertByTime_perm (q e) : (insertByTime q e).Perm (e :: q)
theorem deliver_sorted : c.pending.Sorted (·.time ≤ ·.time) → ... c'.pending.Sorted ...
```
Then format 2's head is the calculus's label 0, and the remaining nondeterminism is only among
equal-time prefixes (which also shrinks the M2.6/M4 state space).

## 9. `Err.shape` reachable; no shape invariant (SHOULD-FIX)

Without `Sys.WF`, a malformed `init` makes every delivery fail with `shape`. Demo D5:
```lean
def badF4 : Sys := { f4AB with init := { f4Init with machines := [⟨0, [.int 0]⟩] } }
example : (deliver badF4 badF4.init 0).map sm = some (.inl .shape) := by decide
```
This is conservative (errors are counterexamples), and the step preserves shape (`set` checks the index,
`fireOne` sets `ctrl` to a `Fin`), but that is not stated, so every invariant proof over a general system
must re-derive it, and `deliver` can never be shown to avoid `shape`. Values that do not fit their
declared sort in `init` (a `bool` variable holding `.int 5`) are likewise unchecked. Add:
```lean
def Cfg.Shaped (sys : Sys) (c : Cfg) : Prop :=
  c.machines.length = sys.sig.machines ∧ ∀ m : Fin sys.sig.machines, ∃ ms, c.machines[m.val]? = some ms ∧
    ms.ctrl < (sys.sig.states m).length ∧ List.Forall₂ (fun v τ => v.fits τ) ms.vars (sys.sig.vars m)
theorem shaped_invariant (h : sys.init.Shaped sys) : (Sys.lts sys).Invariant (fun s => s.cfg.Shaped sys)
theorem deliver_ne_shape (h : c.Shaped sys) : deliver sys c k ≠ some (.error .shape)
```
(the last also needs `vars`-length preservation; the `Forall₂ fits` part needs finding 3/6).

## 10. The f4 invariants (NOTE)

`f4_ab_safe`/`f4_ba_safe` are not vacuous (`f4_nonVacuous`) nor trivially true: under `deliverNext`,
`f4AB` reaches `y = 1`. But each is a two-state system decided by one `decide` on `deliver`; they test
the definition of `deliver` on one input. The two-verdict side is a single-step computation (`afterNext`),
not an LTS invariant refuted under a `Sys.ltsNext`. The general "one verdict" (foundations M2 done-when)
is a renaming theorem, which needs finding 1 first because renaming changes emission order:
`theorem lts_rename (π : Equiv.Perm (Fin n)) : (Sys.lts (sys.rename π)) ≈ (Sys.lts sys)` (bisimilar
via permuting `machines` and pending Perm).

## 11. Labels are positions (NOTE, blocks M5)

A label is an index into a list that shifts under `eraseIdx` and append; "entry x is eventually
delivered" (weak fairness per entry) cannot be expressed with it, and equal entries give two labels to
one successor. Plan 2.3's `Label` keeps this. Before M5, label by the entry (`Entry` with `src` from M2.2)
or carry a stable id that the abstraction erases.

## 12. Smaller fidelity gaps (NOTE, M2.4/M2.5)

* `==`/`!=` across sorts: format 2 gives `false`/`true` (`eqv`, Expr.lean:340-341), the calculus
  `Err.sort` (Behav.lean:274). Excluded only if elaboration rejects ill-typed comparisons (needs WF).
* `str + str` concatenates in format 2 (Expr.lean:343-346); `Err.sort` here.
* No `>`/`>=`; encoding as swapped `<`/`<=` changes which operand is evaluated first, hence which error
  is reported (format 2: left first, Expr.lean:338-339).
* Which error is reported depends on winner order (acknowledged); M2.5 differential traces compare
  error messages.
* Entries have no target: a format-2 reply or timer entry addressed to one instance is delivered to all
  machines here (M2.2 adds `target`).

## 13. Composition (NOTE, M6)

`Sys` is closed (no input/output alphabets; events are broadcast `Nat`s), and `Ref.other m v` with
`v : Fin (S.vars m).length` is dependently scoped, so a product of two systems needs a re-indexing of
`Expr` along `Fin.append`-style casts. Not blocking now; worth a `Sig.append` and `Expr.lift` sketch
before M2.4 freezes the syntax.

## What is correct

* `phase2_perm`, `phase2_perm_emitted`, `phase2_swap`, `phase2_perm_from`: proofs sound; `phase2_perm`
  also gives "fails in one order iff in every order" (both sides `none`), as the claim says.
* Errors are states (`outcome`, `err_deadlocked`); `divZero_counterexample` is the right regression test.
* Snapshot reads are by construction (`ctxOf c e own`), guards on the snapshot, own variables threaded.
* Spec `about` lists: `behav-phase2-order-independent` (phase2), `behav-f4-*-safe` (Sys.lts, f4AB/f4BA,
  Invariant), `behav-failed-step-is-counterexample` (Sys.lts, Invariant) all name constants of their
  statements; only 7 is off.
