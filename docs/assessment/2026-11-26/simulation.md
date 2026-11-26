# Simulation science and empirical validation: assessment

Scope: formal/Exegra/{Format2,Workload,Random,Resource,Number}.lean, src/core/{distributions,metric-claims,metric-stats,telemetry,fault-model,pools,readiness-time}.js, docs/simulation.md, spec components simulation-engine / workload-model / metric-claims, WG-4663.
Demonstration scripts (pure JS, using the repository's own modules): demos/metric-demo1.mjs, demo2.mjs, demo3.mjs. Lean was not run; Lean conclusions come from reading the source.

## 1. Verdict

The foundation can be evolved. It does not need a rewrite. The representation choices are sound and unusually disciplined: integer time in a declared base unit, `Nat` arithmetic, exact rationals for rates, integer inverse-CDF tables, addressable SplitMix64 streams, and exact BigInt binomial tests. The vocabulary also keeps the right distance from verification: `model-holds` is never `verified` or `supported`, and "probability is not nondeterminism" is a stated principle.

What is missing is foundation, not repair:
- There is no measure-theoretic semantics. Lean defines only the run for a fixed seed.
- No theorem links the sampled tables to the distributions they are supposed to realise.
- The statistical layer is JavaScript, outside Lean.
- Fidelity (guarantee class 8) exists only as a design. Calibration, envelope, sensitivity and revision binding are explicitly "Not built (WG-4741)".

Three defects in the statistics path let `model-holds` claim more than the evidence supports (section 2).

## 2. Fundamental limitations, unsound assumptions, missing foundations

**F1. Underpowered runs are always left out, for every workload kind. Collapsing runs disappear instead of failing.**
- Severity: BLOCKS-OBJECTIVE for the statistical claims. Status: DEMONSTRATED.
- What the docs require: docs/simulation.md "Request lifecycle" and "Sample counts and underpowered runs", and the spec claim `metric-claims-report-basis`, say an underpowered run is left out *only* for an open-started class. For any other class it "does not satisfy, so a collapse can never turn fails into inconclusive".
- What the code does: src/core/metric-claims.js:148 sets `openStarted: claim.openStarted !== false`. The only caller, src/core/claims.js `evaluateMetricBound` (about lines 437-441), builds `claim` without an `openStarted` field. Nothing in src/, cli/ or tools/ ever computes open-startedness (grep finds `openStarted` only in metric-claims.js, metric-stats.js and tests). So `metric-stats.js:181` drops every underpowered run, closed and population workloads included.
- Counterexample (demo1.mjs): 100 runs of a closed-workload class. 60 normal runs have p99 = 20 ms ≤ 30 ms. 40 runs collapse: 12 requests measured, p99 = +∞, underpowered because 12·0.01 < 30.
  - As evaluated: `holds`, kept 60, left out 40, status **model-holds**.
  - As specified (`openStarted:false`): `fails`, status **violated**.
  - The true per-run violation probability is 40%.
- Open-started classes are not exempt either. A request whose key matches an unended request of the same class is not started; it is counted `duplicate` (Format2.lean:2780). So with keys drawn from a small payload pool, a stalled system lowers `n`. That makes `n` depend on the system, not only on arrivals, which contradicts the doc's justification ("n depends only on the arrivals"). A stall then becomes "underpowered, left out" here too. This variant is ARGUED.

**F2. The tool's own "runs to decide" advice is optional stopping. It inflates the false-holds rate past α.**
- Severity: LIMITS. Status: DEMONSTRATED.
- `evaluateRuns` returns `decideAt = runsToDecide(...)` for inconclusive results (metric-stats.js:228, :134-138). The docs say "the result says how many runs would decide an inconclusive one". The same docs also say N "is fixed before the runs and never extended after seeing results". Nothing enforces that: `runs` and `seed` are plain spec fields.
- Rerunning with N = decideAt and the same base seed replays the earlier runs as a prefix, because run seeds are `runSeed(s, r)`. That is sequential testing.
- demo3.mjs (thresholds from the repository's exact `runsToDecide`: 59, 93, 124, 153, 181, 208, 234):

  | True per-run pass probability | One-shot false-holds | Following decideAt |
  |---|---|---|
  | 0.95 (boundary) | 4.85% | **13.5%** |
  | 0.945 | 3.6% | 8.8% |
  | 0.94 | 2.6% | 5.8% |

  Nominal α is 5%.
- Seed shopping is unrestricted too. At p = 0.94, trying 114 base seeds gives a 95% chance of a `holds`.
- The guarantee is a frequentist statement about a seed chosen independently of the model. A fixed, recorded base seed makes the verdict deterministic. Tuning parameters against that seed overfits to it, and Exegra neither records nor prevents it (no pre-registration, no seed derived from a commitment hash).

**F3. There is no semantics of a distribution over runs. Lean has only `seed ↦ run`.**
- Severity: BLOCKS-OBJECTIVE for classes 4 and 8 in their probabilistic form. Status: ARGUED.
- Random.lean proves only `uniformInt_ge` and `uniformInt_le` (range). Everything else is `#guard` test vectors.
- Workload.lean proves only `nextTime_lt_horizon`. `interarrival` and `isqrt` have no correctness theorem. The doc claims they invert the integrated rate exactly and round half up; that is not proved.
- Nothing states "if the draws are i.i.d. uniform on 2^64, then `sampleTable r pts` has CDF F_pts" or "arrivals form a Poisson process of rate λ(t)". There is no PMF/measure monad, no pushforward, no definition of "the probability that a run satisfies φ", which is the parameter the binomial test estimates.
- So the statistical claim is about an object Lean never defines. The i.i.d. premise is the assumption `seeded-streams-independent` (spec.jsonc:14691), honestly labelled "tested, not proved".

**F4. Distribution semantics live in JavaScript and in the input. The engine trusts whatever table it is handed.**
- Severity: LIMITS (it conflicts with "Lean sole authority"). Status: DEMONSTRATED by source.
- Qexp, Qnorm, exp_fp, ln_fp and every family lowering are in src/core/distributions.js. Format2.lean `unitExp` (around line 581) checks only that `u` runs from 0 to 2^32, `u` strictly increases and `x` does not decrease. The documented SHA-256 pin `a23cd2a9…` is checked only in tests/core/distributions.test.js:27, never when an input is read.
- So `[[0,0],[2^32, 2^64]]` is accepted as "unit exponential": a Poisson workload silently becomes uniform interarrivals.
- The "correctly rounded at all 1,045 points" claim rests on an external 80-digit computation, not a proof.

**F5. Lowering bias is real, uncorrected outside fixtures, and unbounded by any theorem.**
- Severity: MINOR to LIMITS. Status: DEMONSTRATED (demo2.mjs, exact `tableMean`).
- Exponential: table mean is −4.3% at mean 1 base unit, −1.4% at 2, −0.34% at 10, −0.15% at 100. This is a systematic −0.35 to −0.5 base units per sample, from rounding plus the floor in `sampleTable`. Poisson workloads refuse mean interarrivals below 100 base units (Format2.lean:2595). Service or latency distributions have no such guard and no warning.
- Lognormal: table mean is +3.1% at σ = 3 and +5.3% at σ = 4, because linear interpolation of a convex tail overestimates. It is −13.2% at median 1, σ = 5.5, because the tail is truncated at p = 1 − 2^-32. `sigma ≤ 8` is "allowed", but at σ = 8 every median exceeds the 2^53 bound.
- Empirical `{samples}`: values that were never observed occur with probability 1/1024, from interpolation across grid cells.
- The docs state only the bias of Qexp itself (+1.18e-4), which has the opposite sign to the bias of the lowered integer tables.

**F6. The documented "accumulated metric exceeds 2^53" failure is not implemented. Metrics are silently rounded.**
- Severity: MINOR. Status: DEMONSTRATED by source.
- docs/simulation.md:379 promises a failed step `Value metric <name> exceeds 2^53` / `counter <name>`.
- The only "exceeds" checks in Lean are for time and service time (Format2.lean:1346-1717). Rust has none for metrics.
- Metrics are emitted through `def n (k : Nat) := .num k.toFloat` (Format2.lean:2826; used at :2993-3005). Payload counters use `.num n.toFloat` (:1835).
- Example: unit `ns`, a 10 s window and a queue of about 900,001 waiting gives `queueLength.integral` ≈ 9.0e15 + odd. That is reported rounded to a double, and metric-claims.js then takes `BigInt` of the rounded number. The numeric effect is tiny, but it breaks the "every number is an exact integer" contract.

**F7. Fidelity (class 8) has no implementation.**
- Severity: BLOCKS-OBJECTIVE. Status: DEMONSTRATED.
- The metric-claims unknowns say "Not built: calibration, sensitivity, the operating envelope and revision binding (asOf is only recorded) (WG-4741)".
- In practice: no `load-run` evidence kind, no `calibratedBy` evaluation, no error model, no provenance on observed data, no validity domain.
- The design in docs (hold-out bands, sign-test interval inside the band, convex-hull envelope, sensitivity) is a reasonable plan. Even so, it gives only "agrees within a tolerance on the tested points". It gives no quantified prediction error elsewhere and no propagation of parameter uncertainty into the verdict, beyond a one-at-a-time and pairwise flip test.

**F8. A per-run statistic plus fraction β is not a safety property.**
- Severity: LIMITS. Status: ARGUED.
- At the defaults, `model-holds` tolerates a per-run catastrophe probability of up to 5%. A per-run p99 concentrates as the horizon grows, so "95% of runs" means something different at each horizon.
- β → 1 is impossible in practice: β = 0.999 needs N ≥ 2995.
- The docs state this, but the claim statement texts read as properties ("p99 … is at most 30 ms").

## 3. Overclaims

- **Underpowered runs.** `metric-claims-report-basis` (spec) and docs say underpowered runs are "left out only for an open-started class". The code always leaves them out (F1). The metric-claims component `responsibilities` assert the same.
- **Open-started `n`.** docs/simulation.md says for open-started classes "n depends only on the arrivals". This is false under the `duplicate` rule (F1).
- **Accumulated metrics.** docs:379 promises a failed step on accumulated metric or counter overflow. It is not implemented (F6).
- **Hash pin.** The "Hash" paragraph of docs "Lowering" reads as a pin on engine input. It is enforced only in a unit test (F4).
- **Workload.lean header.** It says "Poisson instants invert the integrated rate exactly". The computation is exact integer arithmetic, but there is no theorem that the result is the inverse; only two `#guard`s (F3).
- **Independence wording.** docs "Claims over metrics" says "Runs with distinct seeds draw from disjoint streams, so their per-run statistics are independent and identically distributed". Distinct keys do not make streams disjoint: two SplitMix64 streams overlap whenever k2 − k1 ≡ jγ mod 2^64. They are pseudorandom, not independent. The text then cites the assumption correctly; the "so" is the overclaim.
- **No false "verified".** None found on the metric path: `claimStatus` never returns `verified` or `supported`, and claims.js scope strings say "Never verified, never counted as evidence". The fixture claims (`metrics-reproduce-mm1-utilisation` and others) are correctly *not evaluated*.

## 4. What to preserve

- **Integer time, `Nat` metrics, exact-rational rates and bounded inputs** (docs "Integers and bounds", "Time"; Format2 decoding). The decision is correct for an explorer that needs exact simultaneity and for bit-for-bit differential checking. The stated rejection of rational and floating time is well argued.
- **Addressable SplitMix64 streams** keyed by (stream name, index), with counters in the configuration (Random.lean). Draws stay stable under model edits, explorer states stay small, and the reference vectors are pinned with `#guard`. This is the right substrate for later reasoning about randomness as a function of seed.
- **The integer, bit-specified distribution lowering** (distributions.js) and exact `tableMean`. Being reproducible and exactly analysable is what makes F5 measurable at all.
- **The exact binomial (Clopper-Pearson) and sign-test machinery** in metric-stats.js, all BigInt and without floating point. The run is the unit of independence, which correctly avoids pooling autocorrelated within-run samples. Negatives and control negatives add a vacuity check.
- **The status lattice.** `model-holds`, `unvalidated` and `extrapolated` are distinct from `supported` and `verified`. The static "verified only with no drawing element" criterion (docs "Exploration and sampling") keeps "verified simulator" separate from "accurate simulator".
- **Number.lean.** It converts decimal text to double and computes fmod exactly from bit patterns. I found no error on reading it.
- **The Resource.lean invariants** (capacity and class-limit bounds, no sorry). They are safety facts about the semantics, independent of probability.

## 5. Architectural decisions that would prevent the objective, and replacements

1. **The statistical verdict is computed in JavaScript** (metric-stats.js is tagged `verdict-kernel`, inside the known `core-logic-in-lean` gap). Replacement: port the tests to Lean on `Nat`/`Rat`, with a theorem relating `binomialVerdict` to the Clopper-Pearson bound.
2. **Distributions defined outside Lean and trusted as input tables.** Replacement: Lean owns the family semantics. Lean recomputes or verifies the table (at least the pinned hash) when an input is read, and proves monotonicity of the table and its CDF relation.
3. **Seed and N as freely editable parameters with no commitment.** Replacement: derive the base seed from a hash of the claim plus the model revision, or record seed history. Refuse N changes that follow an inconclusive result. Remove `decideAt` advice, or turn it into a properly alpha-spent sequential test (for example a group-sequential or SPRT design).
4. **A run-only semantics with no probability space.** Replacement: a `PMF`/measure-valued semantics. Treat the seed as uniform over `UInt64^streams`, or idealise the draws as i.i.d. uniform with an explicit assumption. Define `P[φ]` and prove that the per-run Bernoulli the test consumes is that probability under the idealisation.
5. **Fidelity treated only as tolerance bands.** Replacement: observed data as typed evidence with provenance (system revision, workload, instrument, timestamp) and an explicit error model. Report validity domains and predictive error bounds as first-class parts of a claim result.

## 6. Highest-leverage foundational changes (dependency order)

1. **Fix F1 and F6. They are cheap and they restore honesty now.**
   - Change: compute open-startedness from the input (every start event of the class comes from an open workload) and pass it in. Count `duplicate` starts toward `n`, or treat a run with duplicates as not open-started. Add the 2^53 metric and counter checks in Lean and Rust.
   - Done when: demo1's 100-run scenario on a closed workload reads `violated` through `evaluateMetricBound`; a regression test turns a stalled open-workload run with duplicate keys into a non-pass; a fixture with integral ≥ 2^53 fails the step with `Value metric … exceeds 2^53.`
2. **Commit to seeds and N.**
   - Change: base seed = hash(claim id, model semantic hash) unless overridden with a recorded reason; N immutable after a result; drop or alpha-spend `decideAt`.
   - Done when: demo3's strategy can no longer be executed through the CLI, and a test shows the false-holds rate at p = β is ≤ α under the permitted workflow.
3. **Lean ownership of distributions.**
   - Change: Lean checks the unit-exponential and family tables (hash or recomputation) at decode time. Prove `sampleTable` monotone in `r`, and that `P_{u*~U[0,2^32)}[sampleTable ≤ x]` equals the piecewise CDF of the table. Prove `isqrt` correct and `interarrival` the rounded root of the integrated-rate equation.
   - Done when: Lean theorems exist with no sorry; a bogus `unitExponential` input is refused; an exact bias bound per family is stated as a theorem (or at least as a checked lemma over `tableMean`).
4. **A probability semantics.**
   - Change: `runDist : Input → PMF Trace` under idealised i.i.d. uniform draws, with `run seed` as its sampling realisation; `P[statistic satisfies bound]` defined; a theorem that the binomial verdict is a valid level-α test of `P ≥ β` given i.i.d. Bernoulli inputs. This needs Mathlib's `PMF` or an in-house finite-support version.
   - Done when: the theorem exists in Lean and metric-stats.js is ported to Lean, with the JS kept only as a differential mirror.
5. **Fidelity (WG-4741) with quantified error.**
   - Change: `load-run` evidence with provenance and an instrument-error model; calibrate on fitting runs, test on hold-out runs; report a validity domain (envelope) and the measured prediction error per statistic; let parameter uncertainty propagate into the verdict, not only through flip tests.
   - Done when: at least one Exegra-self claim (for example a claim-evaluation latency) is calibrated against recorded measurements and reports `validated` or `unvalidated` with its envelope, and changing the component revision automatically turns it `unvalidated`.

## 7. Predictions about other teams

- **Verification and formal teams** will see "Lean semantics for format 2, run differentially against Rust" and conclude that the simulator is verified. What exists is a deterministic per-seed semantics with a few bound lemmas. No theorem covers distributions, arrival processes or metrics against their docs, and agreement with Rust is agreement, not correctness.
- **Claims and evidence teams** will praise `model-holds` as never overclaiming. It is mostly right as a label, but they will miss F1: the label can be reached by dropping exactly the failing runs. They will also miss that the recorded seed makes the "95% confidence" a one-shot frequentist statement that Exegra does not protect (F2).
- **Architecture and change-impact teams** will treat `asOf`, `calibratedBy` and revision binding as present, because they are in the schema (claim-methods.js:148) and in the docs. `asOf` is only echoed, and calibration and binding are not built.
- **Some reviewers will call integer time a fidelity limitation.** It is not one: microseconds with a 2^53 bound are fine. The real numeric bias is in the integer lowering (F5) and the floor interpolation, at small base-unit means.
- **Optimists will read the long docs section on calibration and the operating envelope as a fidelity capability.** It is a design. Class 8 is at zero implementation.
