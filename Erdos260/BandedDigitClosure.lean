import Erdos260.Erdos260PushCapstone
import Erdos260.ReturnCleanCarryCore
import Erdos260.FailingShellPeriodicityCore

/-!
# Banded digit closure — the escape-time / below-band collapse of the wave-8 digit fields
(`BandedDigitClosure`)

The wave-8 capstone (`Erdos260PushCapstone`) banded the two digit-valued Return fields:
`ReturnZeroBodyBanded` / `ReturnMaxCleanBodyBanded` demand the zero digit only at positions
whose carry sits at/above the lower band edge `Q·(N+1) ≤ 2·R_N` (below-band positions are
closed free by `digit_forced_zero_of_carry_low` through `ctx.hrational`).  This module
converts the recorded band dynamic — each forced zero DOUBLES the carry
(`R_{N+1} = 2 R_N` when `d_{N+1} = 0`, the recurrence of `IntegerCarry`) — into theorems
about the banded fields.

## 1.  The escape-time argument (exact, formalized)

From a position `N` with band carry (`Q·(N+1) ≤ 2·R_N`), a zero run on `(N, N+h]` doubles
the carry `h` times (`integerCarry_add_of_zero_digits`), and the envelope
`R_{N+h} ≤ Q·(N+h+2)` (`integerCarry_bounds_of_rational_value`) caps the growth.  The exact
bound (`band_zeroRun_envelope`):

> `2^h · (N+1) ≤ 2 · (N+h+2)`.

Consequences: `h ≤ 3` always (`band_zeroRun_le_three`), `h ≤ 1` for `N ≥ 3`
(`band_zeroRun_le_one_of_deep`), and the explicit escape function
`bandEscapeH N = 3, 2, 2, 1, 1, …` (`band_zeroRun_le_bandEscapeH`).  So a band-carry
position can be followed by at most `bandEscapeH N` demanded zeros — the carry escapes
through the band top in at most 3 steps, where `digit_forced_one_of_carry_high` refutes
any further zero.

## 2.  The collapse: digit fields ⟺ pure carry-trajectory statements

* **Unconditional, all positions** (`returnZeroBody_iff_cleanDoubling`): the verbatim
  `ReturnZeroBody` is EQUIVALENT to the pure carry statement "every demanded slice
  interval doubles cleanly": `carryOf z = 2^(z−x) · carryOf x` — no digit content at all
  (per-interval engine: `cleanReturnSegment_iff_zeroRun`).
* **The below-band trajectory form** (`zeroRun_iff_belowBand_trajectory`, for `x ≥ 3`;
  body level `returnZeroBody_iff_belowBandTrajectory` under `OlcFibreDeep`): zeros on
  `(x, z]` ⟺ the carry sits STRICTLY BELOW BAND at every `N ∈ [x, z−2]` AND the final
  step doubles (`carryOf z = 2 · carryOf (z−1)`).  HONEST CORRECTION to the naive guess:
  the demand is NOT equivalent to below-band on ALL of `[x, z−1]` — at the final position
  `z−1` the carry may sit inside the band `[Q·z, Q·(z+2)]` with the zero digit at `z`
  still consistent; the final step survives as a carry-doubling equation (still pure
  carry, zero digit content).  The unconditional variant
  (`zeroRun_iff_belowBand_trajectory_uncond`) needs no `x ≥ 3`: below-band at every
  `N ∈ [x, z−4]` plus clean tail doubling over the last `≤ 3` steps.
* `returnMaxCleanBody_iff_carryTrajectory` (unconditional): the clean step at per-slice
  maxima is EQUIVALENT to `carryOf (k+1) = 2 · carryOf k` — pure carry, no caveat.

## 3.  Below-band trajectory bounds (the dangerous link checked)

`ActualFailureContext` carries `hrational` AND `hnonterm` as fields at EVERY ctx
(`UnconditionalTheorem.lean`), so `carryOf ctx N > 0` at EVERY index (`carryOf_pos`,
via `integerCarry_pos_of_not_eventuallyZero` — NO onset restriction; the only
onset-limited forcing is the parity one, unused here).  Hence:

* `belowBand_pow_lt`: a strictly-below-band run `[x, z)` forces `2^(z−x) < Q·z` —
  below-band intervals are log-short (`belowBand_length_le_log`: `z−x ≤ log₂(Q·z)`).
* `zeroRun_pow_le_envelope`: ANY satisfiable zero demand on `(x, z]` forces
  `2^(z−x) ≤ Q·(z+2)` (`returnZeroBody_interval_le_log`: demanded slice intervals are
  log-short, unconditionally).
* `sameSlice_gap_pow_le` + `returnZeroBody_sameSlice_doubleExp`: same-slice pairs obey
  `2^(carryVal2 x) ∣ z−x` (`returnSelfRefKey_gapDiv`), so a satisfiable demand needs
  `2^(2^(carryVal2 x)) ≤ Q·(z+2)`; the refutation
  `returnZeroBody_refuted_of_sameSlice_doubleExp` kills the demand whenever
  `Q·(z+2) < 2^(2^(carryVal2 x))`.  HONEST: this does NOT close the fields outright —
  `carryVal2 x` can be `0` (odd carry), and in the demanded regime the capstone guard
  even bounds `2^(carryVal2 k) < (supportShell …).card` from ABOVE; no in-tree positive
  lower bound on `carryVal2` at fibre members exists, so slices are not forced singleton.

## 4.  Deliverable

The successor surface `ReturnDigitTrajectorySurface` (the two digit fields in pure
carry-trajectory form, same guards), the bridges into the capstone field shapes
(`pushResidual_returnZero_field_of_trajectory` / `pushResidual_returnMaxClean_field_of_trajectory`),
the combinator `pushResidual_withTrajectoryDigits`, and the endpoint
`erdos260_of_trajectoryDigits`.  Strength accounting: trajectory ⟹ banded is
UNCONDITIONAL; the converse holds per-ctx under `OlcFibreDeep` (all fibre members `≥ 3`,
`trajectorySurface_of_pushResidual`); the `returnMaxClean` lane is equivalent with no
caveat.  Additive only; no upstream module touched.  No `sorry`, no `admit`, no new
`axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Band predicates and the per-step digit/carry dictionary -/

/-- The carry at `N` sits strictly below the lower envelope band edge:
`2·R_N < Q·(N+1)`.  Here the next digit is forced to `0` unconditionally. -/
def StrictlyBelowBand (ctx : ActualFailureContext) (N : ℕ) : Prop :=
  2 * carryOf ctx N < (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ)

/-- The carry at `N` sits at/above the lower band edge: `Q·(N+1) ≤ 2·R_N`.  This is
exactly the band condition under which `ReturnZeroBodyBanded` demands the zero digit
at `N+1`. -/
def BandAtOrAbove (ctx : ActualFailureContext) (N : ℕ) : Prop :=
  (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ) ≤ 2 * carryOf ctx N

/-- The two band states are an exact dichotomy (negation form). -/
theorem bandAtOrAbove_of_not_strictlyBelowBand {ctx : ActualFailureContext} {N : ℕ}
    (h : ¬ StrictlyBelowBand ctx N) : BandAtOrAbove ctx N := by
  unfold StrictlyBelowBand at h
  unfold BandAtOrAbove
  exact not_lt.mp h

/-- The two band states are an exact dichotomy (disjunction form). -/
theorem strictlyBelowBand_or_bandAtOrAbove (ctx : ActualFailureContext) (N : ℕ) :
    StrictlyBelowBand ctx N ∨ BandAtOrAbove ctx N := by
  by_cases h : StrictlyBelowBand ctx N
  · exact Or.inl h
  · exact Or.inr (bandAtOrAbove_of_not_strictlyBelowBand h)

/-- The actual carry is the integer carry at the chosen numerator (definitional). -/
theorem carryOf_eq_integerCarry (ctx : ActualFailureContext) (N : ℕ) :
    carryOf ctx N = integerCarry ctx.Q (ctxNum ctx) ctx.d N := rfl

/-- **The rational numerator is unique**: any `P` witnessing `ctx.hrational` equals
`ctxNum ctx`.  So the `∀ P` quantification inside the banded bodies ranges over exactly
one value, and the band condition there IS `BandAtOrAbove`. -/
theorem ctxNum_unique (ctx : ActualFailureContext) {P : ℤ}
    (hP : realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (ctx.Q : ℝ)) :
    P = ctxNum ctx := by
  have hQ : ((ctx.Q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp ctx.hQ)
  have h : (P : ℝ) / (ctx.Q : ℝ) = ((ctxNum ctx : ℤ) : ℝ) / (ctx.Q : ℝ) :=
    hP.symm.trans (ctxEta ctx)
  have h2 : (P : ℝ) = ((ctxNum ctx : ℤ) : ℝ) := by
    have h3 := congrArg (fun t : ℝ => t * (ctx.Q : ℝ)) h
    simpa [div_mul_cancel₀, hQ] using h3
  exact_mod_cast h2

/-- The integer carry at ANY rational-value witness is the actual carry. -/
theorem integerCarry_value_eq_carryOf (ctx : ActualFailureContext) {P : ℤ}
    (hP : realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (ctx.Q : ℝ)) (N : ℕ) :
    integerCarry ctx.Q P ctx.d N = carryOf ctx N := by
  rw [ctxNum_unique ctx hP, carryOf_eq_integerCarry]

/-- **The banded bodies' band condition is exactly `BandAtOrAbove`** at the predecessor
position — the `∀ P` in `ReturnZeroBodyBanded` hides nothing. -/
theorem bandedDemand_band_iff (ctx : ActualFailureContext) {P : ℤ}
    (hP : realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (ctx.Q : ℝ))
    {j : ℕ} (hj : 1 ≤ j) :
    ((ctx.Q : ℤ) * (j : ℤ) ≤ 2 * integerCarry ctx.Q P ctx.d (j - 1))
      ↔ BandAtOrAbove ctx (j - 1) := by
  rw [integerCarry_value_eq_carryOf ctx hP]
  unfold BandAtOrAbove
  have hjj : j - 1 + 1 = j := by omega
  rw [hjj]

/-- **Strictly below band forces the zero digit** (wrapper of
`digit_forced_zero_of_carry_low` at the actual carry). -/
theorem digit_zero_of_strictlyBelowBand (ctx : ActualFailureContext) {N : ℕ}
    (h : StrictlyBelowBand ctx N) : ctx.d (N + 1) = 0 := by
  unfold StrictlyBelowBand at h
  rw [carryOf_eq_integerCarry] at h
  exact digit_forced_zero_of_carry_low ctx.hQ ctx.hd (ctxEta ctx) h

/-! ## Part 1.  The escape-time argument

A band-carry position followed by demanded zeros doubles the carry out through the
envelope top in at most `bandEscapeH N ≤ 3` steps. -/

/-- **The exact escape-time envelope.**  From a band-carry position `N`
(`Q·(N+1) ≤ 2·R_N`), a zero run on `(N, N+h]` forces `2^h · (N+1) ≤ 2 · (N+h+2)`:
the doubled carry `R_{N+h} = 2^h·R_N ≥ 2^h·Q·(N+1)/2` must fit under the upper envelope
`R_{N+h} ≤ Q·(N+h+2)`. -/
theorem band_zeroRun_envelope (ctx : ActualFailureContext) {N h : ℕ}
    (hband : BandAtOrAbove ctx N)
    (hz : ∀ j, N < j → j ≤ N + h → ctx.d j = 0) :
    2 ^ h * (N + 1) ≤ 2 * (N + h + 2) := by
  unfold BandAtOrAbove at hband
  have hdoub : carryOf ctx (N + h) = 2 ^ h * carryOf ctx N := by
    simp only [carryOf_eq_integerCarry]
    exact integerCarry_add_of_zero_digits ctx.Q (ctxNum ctx) ctx.d N h hz
  have hub : carryOf ctx (N + h) ≤ (ctx.Q : ℤ) * ((N + h + 2 : ℕ) : ℤ) := by
    rw [carryOf_eq_integerCarry]
    exact (integerCarry_bounds_of_rational_value (N + h) ctx.hQ ctx.hd (ctxEta ctx)).2
  have hQpos : (0 : ℤ) < (ctx.Q : ℤ) := by exact_mod_cast ctx.hQ
  have hchain : (ctx.Q : ℤ) * ((2 : ℤ) ^ h * ((N + 1 : ℕ) : ℤ))
      ≤ (ctx.Q : ℤ) * (2 * ((N + h + 2 : ℕ) : ℤ)) := by
    calc (ctx.Q : ℤ) * ((2 : ℤ) ^ h * ((N + 1 : ℕ) : ℤ))
        = (2 : ℤ) ^ h * ((ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ)) := by ring
      _ ≤ (2 : ℤ) ^ h * (2 * carryOf ctx N) :=
          mul_le_mul_of_nonneg_left hband (by positivity)
      _ = 2 * ((2 : ℤ) ^ h * carryOf ctx N) := by ring
      _ = 2 * carryOf ctx (N + h) := by rw [hdoub]
      _ ≤ 2 * ((ctx.Q : ℤ) * ((N + h + 2 : ℕ) : ℤ)) := by linarith
      _ = (ctx.Q : ℤ) * (2 * ((N + h + 2 : ℕ) : ℤ)) := by ring
  have hfin := le_of_mul_le_mul_left hchain hQpos
  exact_mod_cast hfin

/-- Numeric helper: `2h + 4 < 2^h` for `h ≥ 4`. -/
theorem two_pow_gt_linear : ∀ h : ℕ, 4 ≤ h → 2 * h + 4 < 2 ^ h := by
  intro h hh
  induction h with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 4 with hl | hge
      · have hn : n = 3 := by omega
        subst hn
        norm_num
      · have hi := ih hge
        have h2 : 2 ≤ 2 ^ n := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 2 * (n + 1) + 4 = (2 * n + 4) + 2 := by ring
          _ < 2 ^ n + 2 := by omega
          _ ≤ 2 ^ n + 2 ^ n := by omega
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- Numeric helper: `h + 2 ≤ 2^h` for `h ≥ 2`. -/
theorem two_pow_ge_succ_succ : ∀ h : ℕ, 2 ≤ h → h + 2 ≤ 2 ^ h := by
  intro h hh
  induction h with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 2 with hl | hge
      · have hn : n = 1 := by omega
        subst hn
        norm_num
      · have hi := ih hge
        have h2 : 2 ≤ 2 ^ n := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc n + 1 + 2 = (n + 2) + 1 := by ring
          _ ≤ 2 ^ n + 1 := by omega
          _ ≤ 2 ^ n + 2 ^ n := by omega
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **Universal escape time**: from ANY band-carry position, at most `3` consecutive
zeros are possible (`h ≤ 3`; the extremal case is `N = 0`). -/
theorem band_zeroRun_le_three (ctx : ActualFailureContext) {N h : ℕ}
    (hband : BandAtOrAbove ctx N)
    (hz : ∀ j, N < j → j ≤ N + h → ctx.d j = 0) : h ≤ 3 := by
  by_contra hcon
  push Not at hcon
  have henv := band_zeroRun_envelope ctx hband hz
  have haux : 2 * h + 4 < 2 ^ h := two_pow_gt_linear h (by omega)
  have hmul : (2 * h + 5) * (N + 1) ≤ 2 ^ h * (N + 1) :=
    Nat.mul_le_mul (by omega) (le_refl (N + 1))
  nlinarith [henv, hmul]

/-- **Deep escape time**: from a band-carry position `N ≥ 3`, at most ONE zero is
possible (`h ≤ 1`) — the band escape is immediate past the first few positions. -/
theorem band_zeroRun_le_one_of_deep (ctx : ActualFailureContext) {N h : ℕ}
    (hN : 3 ≤ N) (hband : BandAtOrAbove ctx N)
    (hz : ∀ j, N < j → j ≤ N + h → ctx.d j = 0) : h ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have henv := band_zeroRun_envelope ctx hband hz
  have ht : h + 2 ≤ 2 ^ h := two_pow_ge_succ_succ h (by omega)
  have hmul : (h + 2) * (N + 1) ≤ 2 ^ h * (N + 1) :=
    Nat.mul_le_mul ht (le_refl (N + 1))
  have hNh : h * 3 ≤ h * N := Nat.mul_le_mul (le_refl h) hN
  nlinarith [henv, hmul, hNh]

/-- The explicit escape-time function `H(N)`: `H(0) = 3`, `H(1) = H(2) = 2`,
`H(N) = 1` for `N ≥ 3`. -/
def bandEscapeH : ℕ → ℕ := fun N => if 3 ≤ N then 1 else if N = 0 then 3 else 2

/-- **The exact escape-time bound** `h ≤ bandEscapeH N`: a band-carry position is
followed by at most `H(N)` zeros, `H(N) ≤ 3` with `H(N) = 1` from `N = 3` on. -/
theorem band_zeroRun_le_bandEscapeH (ctx : ActualFailureContext) {N h : ℕ}
    (hband : BandAtOrAbove ctx N)
    (hz : ∀ j, N < j → j ≤ N + h → ctx.d j = 0) :
    h ≤ bandEscapeH N := by
  unfold bandEscapeH
  split_ifs with h3 h0
  · exact band_zeroRun_le_one_of_deep ctx h3 hband hz
  · exact band_zeroRun_le_three ctx hband hz
  · by_contra hcon
    push Not at hcon
    have hle3 := band_zeroRun_le_three ctx hband hz
    have hh : h = 3 := by omega
    subst hh
    have henv := band_zeroRun_envelope ctx hband hz
    have hN : N = 1 ∨ N = 2 := by omega
    rcases hN with hN | hN <;> subst hN <;> norm_num at henv

/-! ## Part 2.  Below-band trajectory analysis

Strictly-below-band runs force zeros for free, double the carry, and are therefore
log-short (the carry is POSITIVE at every index: `carryOf_pos`, no onset caveat —
`hrational` and `hnonterm` are fields of every `ActualFailureContext`). -/

/-- **Below-band runs force the zero digits for free.** -/
theorem belowBand_zeroRun (ctx : ActualFailureContext) {x z : ℕ}
    (hbb : ∀ N, x ≤ N → N < z → StrictlyBelowBand ctx N) :
    ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
  intro j hj1 hj2
  have hjj : j - 1 + 1 = j := by omega
  have h := digit_zero_of_strictlyBelowBand ctx (hbb (j - 1) (by omega) (by omega))
  rwa [hjj] at h

/-- **The below-band length bound**: a strictly-below-band run on `[x, z)` forces
`2^(z−x) < Q·z` — the doubled positive carry must stay under the lower band edge,
so below-band intervals are logarithmically short. -/
theorem belowBand_pow_lt (ctx : ActualFailureContext) {x z : ℕ} (hxz : x < z)
    (hbb : ∀ N, x ≤ N → N < z → StrictlyBelowBand ctx N) :
    2 ^ (z - x) < ctx.Q * z := by
  have hz0 : ∀ j, x < j → j ≤ z → ctx.d j = 0 := belowBand_zeroRun ctx hbb
  have hidx : x + (z - 1 - x) = z - 1 := by omega
  have hzr := integerCarry_add_of_zero_digits ctx.Q (ctxNum ctx) ctx.d x (z - 1 - x)
    (fun j hj1 hj2 => hz0 j hj1 (by omega))
  rw [hidx] at hzr
  have hdoub : carryOf ctx (z - 1) = 2 ^ (z - 1 - x) * carryOf ctx x := by
    simp only [carryOf_eq_integerCarry]
    exact hzr
  have hlast := hbb (z - 1) (by omega) (by omega)
  unfold StrictlyBelowBand at hlast
  have hz1 : z - 1 + 1 = z := by omega
  rw [hz1] at hlast
  have hpos : (0 : ℤ) < carryOf ctx x := carryOf_pos ctx x
  have hR1 : (1 : ℤ) ≤ carryOf ctx x := by omega
  have ht : (0 : ℤ) < (2 : ℤ) ^ (z - 1 - x) := by positivity
  have hstep : (2 : ℤ) ^ (z - 1 - x) ≤ (2 : ℤ) ^ (z - 1 - x) * carryOf ctx x :=
    le_mul_of_one_le_right (le_of_lt ht) hR1
  have hexp : (2 : ℤ) ^ (z - x) = 2 * (2 : ℤ) ^ (z - 1 - x) := by
    have hzx : z - x = (z - 1 - x) + 1 := by omega
    rw [hzx, pow_succ]
    ring
  have hfin : (2 : ℤ) ^ (z - x) < (ctx.Q : ℤ) * ((z : ℕ) : ℤ) := by
    calc (2 : ℤ) ^ (z - x) = 2 * (2 : ℤ) ^ (z - 1 - x) := hexp
      _ ≤ 2 * ((2 : ℤ) ^ (z - 1 - x) * carryOf ctx x) := by linarith
      _ = 2 * carryOf ctx (z - 1) := by rw [hdoub]
      _ < (ctx.Q : ℤ) * ((z : ℕ) : ℤ) := hlast
  exact_mod_cast hfin

/-- The below-band length bound in logarithmic form: `z − x ≤ log₂(Q·z)`. -/
theorem belowBand_length_le_log (ctx : ActualFailureContext) {x z : ℕ} (hxz : x < z)
    (hbb : ∀ N, x ≤ N → N < z → StrictlyBelowBand ctx N) :
    z - x ≤ Nat.log 2 (ctx.Q * z) := by
  have h := belowBand_pow_lt ctx hxz hbb
  have hQ0 : ctx.Q ≠ 0 := Nat.pos_iff_ne_zero.mp ctx.hQ
  have hn : ctx.Q * z ≠ 0 := Nat.mul_ne_zero hQ0 (by omega)
  exact Nat.le_log_of_pow_le (by norm_num) (le_of_lt h)

/-- **The escape consequence inside a demanded interval** (deep form): if the digits on
`(x, z]` are all zero with `x ≥ 3`, then the carry sits strictly below band at every
position `N ∈ [x, z−2]` — a band-carry position there would escape in `≤ 1` step,
contradicting the remaining `≥ 2` zeros. -/
theorem zeroRun_belowBand_interior (ctx : ActualFailureContext) {x z : ℕ} (hx3 : 3 ≤ x)
    (hz0 : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ N, x ≤ N → N + 1 < z → StrictlyBelowBand ctx N := by
  intro N hxN hNz
  by_contra hcon
  have hband := bandAtOrAbove_of_not_strictlyBelowBand hcon
  have hrun : ∀ j, N < j → j ≤ N + (z - N) → ctx.d j = 0 :=
    fun j hj1 hj2 => hz0 j (by omega) (by omega)
  have hle := band_zeroRun_le_one_of_deep ctx (by omega) hband hrun
  omega

/-- Reconstruction half: below-band on `[x, z−2]` plus the final clean doubling step
rebuilds the full zero run on `(x, z]` (no deepness needed). -/
theorem zeroRun_of_belowBand_trajectory (ctx : ActualFailureContext) {x z : ℕ}
    (hxz : x < z)
    (hbb : ∀ N, x ≤ N → N + 1 < z → StrictlyBelowBand ctx N)
    (hdz : carryOf ctx z = 2 * carryOf ctx (z - 1)) :
    ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
  intro j hj1 hj2
  rcases Nat.lt_or_ge j z with hjz | hjz
  · have hjj : j - 1 + 1 = j := by omega
    have h := digit_zero_of_strictlyBelowBand ctx (hbb (j - 1) (by omega) (by omega))
    rwa [hjj] at h
  · have hje : j = z := by omega
    have hzz : z - 1 + 1 = z := by omega
    have h := (digit_zero_iff_carry_doubles ctx (z - 1)).2 (by rwa [hzz])
    rw [hzz] at h
    rwa [hje]

/-- **THE PER-INTERVAL COLLAPSE (deep form, `x ≥ 3`)**: the zero demand on `(x, z]` is
EQUIVALENT to a pure carry-trajectory statement — strictly below band on `[x, z−2]`
plus the final clean doubling step `carryOf z = 2·carryOf (z−1)`.  HONEST: the final
position `z−1` may sit INSIDE the band with the zero digit at `z` still consistent, so
the naive "below-band everywhere" is NOT equivalent; the final step survives as a
carry equation (still zero digit content). -/
theorem zeroRun_iff_belowBand_trajectory (ctx : ActualFailureContext) {x z : ℕ}
    (hx3 : 3 ≤ x) (hxz : x < z) :
    (∀ j, x < j → j ≤ z → ctx.d j = 0) ↔
      ((∀ N, x ≤ N → N + 1 < z → StrictlyBelowBand ctx N) ∧
        carryOf ctx z = 2 * carryOf ctx (z - 1)) := by
  constructor
  · intro hz0
    refine ⟨zeroRun_belowBand_interior ctx hx3 hz0, ?_⟩
    have hdz0 : ctx.d z = 0 := hz0 z hxz le_rfl
    have hzz : z - 1 + 1 = z := by omega
    have h := (digit_zero_iff_carry_doubles ctx (z - 1)).1 (by rwa [hzz])
    rwa [hzz] at h
  · rintro ⟨hbb, hdz⟩
    exact zeroRun_of_belowBand_trajectory ctx hxz hbb hdz

/-- **The per-interval collapse, UNCONDITIONAL** (no `x ≥ 3`): the zero demand on
`(x, z]` is equivalent to strictly-below-band at every `N ∈ [x, z−4]` plus clean
doubling over the tail `(max x (z−3), z]` of length `≤ 3` (universal escape `h ≤ 3`). -/
theorem zeroRun_iff_belowBand_trajectory_uncond (ctx : ActualFailureContext) {x z : ℕ}
    (hxz : x < z) :
    (∀ j, x < j → j ≤ z → ctx.d j = 0) ↔
      ((∀ N, x ≤ N → N + 3 < z → StrictlyBelowBand ctx N) ∧
        carryOf ctx z = 2 ^ (z - max x (z - 3)) * carryOf ctx (max x (z - 3))) := by
  constructor
  · intro hz0
    constructor
    · intro N hxN hNz
      by_contra hcon
      have hband := bandAtOrAbove_of_not_strictlyBelowBand hcon
      have hrun : ∀ j, N < j → j ≤ N + (z - N) → ctx.d j = 0 :=
        fun j hj1 hj2 => hz0 j (by omega) (by omega)
      have hle := band_zeroRun_le_three ctx hband hrun
      omega
    · have hxw : x ≤ max x (z - 3) := le_max_left _ _
      have hidx : max x (z - 3) + (z - max x (z - 3)) = z := by omega
      have hzr := integerCarry_add_of_zero_digits ctx.Q (ctxNum ctx) ctx.d
        (max x (z - 3)) (z - max x (z - 3))
        (fun j hj1 hj2 => hz0 j (by omega) (by omega))
      rw [hidx] at hzr
      simp only [carryOf_eq_integerCarry]
      exact hzr
  · rintro ⟨hbb, hdoub⟩ j hj1 hj2
    rcases Nat.lt_or_ge (max x (z - 3)) j with hwj | hwj
    · have hidx : max x (z - 3) + (z - max x (z - 3)) = z := by omega
      have hdoub' : integerCarry ctx.Q (ctxNum ctx) ctx.d
            (max x (z - 3) + (z - max x (z - 3)))
          = 2 ^ (z - max x (z - 3))
            * integerCarry ctx.Q (ctxNum ctx) ctx.d (max x (z - 3)) := by
        rw [hidx]
        simp only [← carryOf_eq_integerCarry]
        exact hdoub
      have hrun := integerCarry_zeroRun_of_doubling ctx.Q (ctxNum ctx) ctx.d ctx.hQ
        (max x (z - 3)) (z - max x (z - 3)) hdoub'
      exact hrun j hwj (by omega)
    · have hjj : j - 1 + 1 = j := by omega
      have h := digit_zero_of_strictlyBelowBand ctx (hbb (j - 1) (by omega) (by omega))
      rwa [hjj] at h

/-- **The unconditional zero-demand length bound** (positivity, no onset caveat):
ANY zero run on `(x, z]` forces `2^(z−x) ≤ Q·(z+2)` — demanded intervals are
log-short whether below band or not (`pow_two_le_of_zero_gap` + `carryOf_pos`). -/
theorem zeroRun_pow_le_envelope (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z)
    (hz0 : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    2 ^ (z - x) ≤ ctx.Q * (z + 2) := by
  have hidx : x + (z - x) = z := by omega
  have hpos : 0 < integerCarry ctx.Q (ctxNum ctx) ctx.d x := by
    rw [← carryOf_eq_integerCarry]
    exact carryOf_pos ctx x
  have h := pow_two_le_of_zero_gap (Q := ctx.Q) (P := ctxNum ctx) (d := ctx.d) (N := x) (h := z - x) ctx.hQ ctx.hd (ctxEta ctx) hpos
    (fun j hj1 hj2 => hz0 j hj1 (by omega))
  rw [hidx] at h
  exact_mod_cast h

/-- **The high-band CONSTRAINT recorded**: along any zero run the carry is confined
under the upper envelope edge, `2·R_{j−1} ≤ Q·(j+2)` (`carry_upper_of_digit_zero`) —
a zero digit is impossible at high band (`digit_forced_one_of_carry_high`). -/
theorem zeroRun_carry_confined (ctx : ActualFailureContext) {x z : ℕ}
    (hz0 : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ j, x < j → j ≤ z → 2 * carryOf ctx (j - 1) ≤ (ctx.Q : ℤ) * ((j + 2 : ℕ) : ℤ) := by
  intro j hj1 hj2
  have hd0 := hz0 j hj1 hj2
  have hjj : j - 1 + 1 = j := by omega
  have h := carry_upper_of_digit_zero (N := j - 1) ctx.hQ ctx.hd (ctxEta ctx)
    (by rwa [hjj])
  have hj3 : j - 1 + 3 = j + 2 := by omega
  rw [hj3] at h
  rw [carryOf_eq_integerCarry]
  exact h

/-! ## Part 3.  The body-level collapse: digit fields as pure carry-trajectory fields -/

/-- Slice members are fibre members. -/
theorem mem_olcFibre_of_mem_olcSlice {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y k : ℕ} (hk : k ∈ olcSlice ctx key y) : k ∈ olcFibre ctx := by
  rw [olcSlice_def] at hk
  exact (Finset.mem_filter.mp hk).1

/-- Slice members share the slice key value. -/
theorem key_eq_of_mem_olcSlice {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y k : ℕ} (hk : k ∈ olcSlice ctx key y) : key k = y := by
  rw [olcSlice_def] at hk
  exact (Finset.mem_filter.mp hk).2

/-- **The `returnZero` demand as a pure carry statement, UNCONDITIONAL**: every demanded
slice interval doubles cleanly, `carryOf z = 2^(z−x)·carryOf x`.  No digit content. -/
def ReturnZeroCleanDoubling (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        x < z → carryOf ctx z = 2 ^ (z - x) * carryOf ctx x

/-- **The `returnZero` demand as a below-band carry trajectory**: on every demanded slice
interval the carry sits strictly below band up to `z−2` and the final step doubles. -/
def ReturnZeroBelowBandTrajectory (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        x < z →
          (∀ N, x ≤ N → N + 1 < z → StrictlyBelowBand ctx N) ∧
          carryOf ctx z = 2 * carryOf ctx (z - 1)

/-- **The `returnMaxClean` demand as a pure carry statement**: the carry doubles across
the step after each per-slice maximum. -/
def ReturnMaxCleanCarryTrajectory (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ olcFibre ctx,
    (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
    carryOf ctx (k + 1) = 2 * carryOf ctx k

/-- All fibre members are deep (`≥ 3`) — the regime hypothesis under which the
below-band trajectory form is EQUIVALENT to the digit field (not just sufficient).
Not proved in-tree; only the positions `0, 1, 2` escape, with escape times `3, 2, 2`. -/
def OlcFibreDeep (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ olcFibre ctx, 3 ≤ k

/-- **`ReturnZeroBody` ⟺ clean doubling (UNCONDITIONAL)** — the verbatim digit field is
a pure carry-trajectory statement; zero digit content remains
(per-interval engine: `cleanReturnSegment_iff_zeroRun`). -/
theorem returnZeroBody_iff_cleanDoubling (ctx : ActualFailureContext) :
    ReturnZeroBody ctx ↔ ReturnZeroCleanDoubling ctx := by
  constructor
  · intro H y hy x hx z hz hxz
    exact (cleanReturnSegment_iff_zeroRun ctx (le_of_lt hxz)).mpr (H y hy x hx z hz hxz)
  · intro H y hy x hx z hz hxz
    exact (cleanReturnSegment_iff_zeroRun ctx (le_of_lt hxz)).mp (H y hy x hx z hz hxz)

/-- Reconstruction (UNCONDITIONAL): the below-band trajectory rebuilds the verbatim
`ReturnZeroBody` — interior zeros from `digit_forced_zero_of_carry_low`, the final zero
from the doubling step. -/
theorem returnZeroBody_of_belowBandTrajectory (ctx : ActualFailureContext)
    (H : ReturnZeroBelowBandTrajectory ctx) : ReturnZeroBody ctx := by
  intro y hy x hx z hz hxz
  obtain ⟨hbb, hdz⟩ := H y hy x hx z hz hxz
  exact zeroRun_of_belowBand_trajectory ctx hxz hbb hdz

/-- **`ReturnZeroBody` ⟺ below-band trajectory under fibre deepness** — at deep fibres
the digit field IS the carry-trajectory statement: the demanded intervals must avoid
band-carry positions entirely except at the final step. -/
theorem returnZeroBody_iff_belowBandTrajectory (ctx : ActualFailureContext)
    (hdeep : OlcFibreDeep ctx) :
    ReturnZeroBody ctx ↔ ReturnZeroBelowBandTrajectory ctx := by
  constructor
  · intro H y hy x hx z hz hxz
    exact (zeroRun_iff_belowBand_trajectory ctx
      (hdeep x (mem_olcFibre_of_mem_olcSlice hx)) hxz).1 (H y hy x hx z hz hxz)
  · intro H
    exact returnZeroBody_of_belowBandTrajectory ctx H

/-- **`ReturnMaxCleanBody` ⟺ carry trajectory (UNCONDITIONAL)** — the per-slice-maximum
clean step is exactly one carry-doubling equation; zero digit content remains. -/
theorem returnMaxCleanBody_iff_carryTrajectory (ctx : ActualFailureContext) :
    ReturnMaxCleanBody ctx ↔ ReturnMaxCleanCarryTrajectory ctx := by
  constructor
  · intro H k hk hmax
    exact (digit_zero_iff_carry_doubles ctx k).1 (H k hk hmax)
  · intro H k hk hmax
    exact (digit_zero_iff_carry_doubles ctx k).2 (H k hk hmax)

/-- `returnMaxClean` is FREE wherever the per-slice maxima sit strictly below band. -/
theorem returnMaxCleanBody_of_belowBand (ctx : ActualFailureContext)
    (h : ∀ k ∈ olcFibre ctx, StrictlyBelowBand ctx k) : ReturnMaxCleanBody ctx :=
  fun k hk _ => digit_zero_of_strictlyBelowBand ctx (h k hk)

/-! ## Part 4.  Slice spacing versus the log-short demand (the honest non-closure) -/

/-- Same-slice pairs are spaced by the self-referential gap: `2^(carryVal2 x) ≤ z − x`
(`returnSelfRefKey_gapDiv` + positivity of the gap). -/
theorem sameSlice_gap_pow_le (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    2 ^ carryVal2 ctx x ≤ z - x := by
  have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
    (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
  exact Nat.le_of_dvd (by omega) (returnSelfRefKey_gapDiv ctx hkey hxz)

/-- **The double-exponential satisfiability bound**: if `ReturnZeroBody` holds, every
same-slice pair `x < z` obeys `2^(2^(carryVal2 x)) ≤ Q·(z+2)` — the forced spacing
collides with the log-short zero run. -/
theorem returnZeroBody_sameSlice_doubleExp (ctx : ActualFailureContext)
    (H : ReturnZeroBody ctx) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → 2 ^ 2 ^ carryVal2 ctx x ≤ ctx.Q * (z + 2) := by
  intro y hy x hx z hz hxz
  have h1 := sameSlice_gap_pow_le ctx hx hz hxz
  have h2 := zeroRun_pow_le_envelope ctx (le_of_lt hxz) (H y hy x hx z hz hxz)
  calc 2 ^ 2 ^ carryVal2 ctx x ≤ 2 ^ (z - x) :=
        Nat.pow_le_pow_right (by norm_num) h1
    _ ≤ ctx.Q * (z + 2) := h2

/-- **Same-slice pair refutation**: a same-slice pair with
`Q·(z+2) < 2^(2^(carryVal2 x))` refutes `ReturnZeroBody` outright.  HONEST: this does
NOT make slices singletons unconditionally — `carryVal2 x` can be `0`, and the
in-regime capstone guard bounds `2^(carryVal2 k)` from ABOVE by the support count. -/
theorem returnZeroBody_refuted_of_sameSlice_doubleExp (ctx : ActualFailureContext)
    {y x z : ℕ} (hy : y ∈ (olcFibre ctx).image (returnSelfRefKey ctx))
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z)
    (hbig : ctx.Q * (z + 2) < 2 ^ 2 ^ carryVal2 ctx x) :
    ¬ ReturnZeroBody ctx := by
  intro H
  have h := returnZeroBody_sameSlice_doubleExp ctx H y hy x hx z hz hxz
  omega

/-- **Demanded slice intervals are log-short**: under `ReturnZeroBody`, every same-slice
pair obeys `z − x ≤ log₂(Q·(z+2))`. -/
theorem returnZeroBody_interval_le_log (ctx : ActualFailureContext)
    (H : ReturnZeroBody ctx) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → z - x ≤ Nat.log 2 (ctx.Q * (z + 2)) := by
  intro y hy x hx z hz hxz
  have h2 := zeroRun_pow_le_envelope ctx (le_of_lt hxz) (H y hy x hx z hz hxz)
  have hQ0 : ctx.Q ≠ 0 := Nat.pos_iff_ne_zero.mp ctx.hQ
  have hn : ctx.Q * (z + 2) ≠ 0 := Nat.mul_ne_zero hQ0 (by omega)
  exact Nat.le_log_of_pow_le (by norm_num) h2

/-- Under `ReturnZeroBody`, the carry is confined under the upper envelope edge along
every demanded interval (the high-band forcing as a recorded constraint). -/
theorem returnZeroBody_carry_confined (ctx : ActualFailureContext)
    (H : ReturnZeroBody ctx) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → ∀ j, x < j → j ≤ z →
            2 * carryOf ctx (j - 1) ≤ (ctx.Q : ℤ) * ((j + 2 : ℕ) : ℤ) := by
  intro y hy x hx z hz hxz
  exact zeroRun_carry_confined ctx (H y hy x hx z hz hxz)

/-! ## Part 5.  Bridges into the capstone surface shapes and the successor surface -/

/-- The below-band trajectory yields the BANDED `returnZero` field body
(unconditional: trajectory ⟹ verbatim body ⟹ banded body). -/
theorem returnZeroBodyBanded_of_belowBandTrajectory (ctx : ActualFailureContext)
    (H : ReturnZeroBelowBandTrajectory ctx) : ReturnZeroBodyBanded ctx :=
  returnZeroBodyBanded_of_full ctx (returnZeroBody_of_belowBandTrajectory ctx H)

/-- The carry trajectory yields the BANDED `returnMaxClean` field body. -/
theorem returnMaxCleanBodyBanded_of_carryTrajectory (ctx : ActualFailureContext)
    (H : ReturnMaxCleanCarryTrajectory ctx) : ReturnMaxCleanBodyBanded ctx :=
  returnMaxCleanBodyBanded_of_full ctx
    ((returnMaxCleanBody_iff_carryTrajectory ctx).2 H)

/-- **Successor surface for the two digit fields**: the `returnZero` / `returnMaxClean`
demands in PURE CARRY-TRAJECTORY form, under the verbatim capstone guards.  No digit
content anywhere. -/
structure ReturnDigitTrajectorySurface where
  /-- The `returnZero` lane: below-band trajectory plus final doubling on every
  demanded slice interval, in the verbatim wave-8 guard regime. -/
  returnZeroTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBelowBandTrajectory ctx
  /-- The `returnMaxClean` lane: one carry-doubling equation per per-slice maximum, in
  the verbatim wave-8 guard regime. -/
  returnMaxCleanTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ReturnMaxCleanCarryTrajectory ctx

/-- **Field bridge** (capstone shape): a trajectory provider fills the
`Erdos260PushResidual.returnZero` slot verbatim. -/
theorem pushResidual_returnZero_field_of_trajectory
    (H : ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      (∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
      ¬ ReturnIndexWindowClean ctx →
      ReturnZeroBelowBandTrajectory ctx) :
    ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      (∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
      ¬ ReturnIndexWindowClean ctx →
      ReturnZeroBodyBanded ctx :=
  fun ctx h1 h2 h3 h4 =>
    returnZeroBodyBanded_of_belowBandTrajectory ctx (H ctx h1 h2 h3 h4)

/-- **Field bridge** (capstone shape): a trajectory provider fills the
`Erdos260PushResidual.returnMaxClean` slot verbatim. -/
theorem pushResidual_returnMaxClean_field_of_trajectory
    (H : ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
      ReturnMaxCleanCarryTrajectory ctx) :
    ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
      ReturnMaxCleanBodyBanded ctx :=
  fun ctx h1 h2 =>
    returnMaxCleanBodyBanded_of_carryTrajectory ctx (H ctx h1 h2)

/-- **The combinator**: replace the two digit fields of any wave-8 surface by a
trajectory provider — the resulting surface is again a full `Erdos260PushResidual`. -/
def pushResidual_withTrajectoryDigits (base : Erdos260PushResidual)
    (S : ReturnDigitTrajectorySurface) : Erdos260PushResidual :=
  { base with
    returnZero := pushResidual_returnZero_field_of_trajectory S.returnZeroTrajectory
    returnMaxClean :=
      pushResidual_returnMaxClean_field_of_trajectory S.returnMaxCleanTrajectory }

/-- **Endpoint**: `Erdos260Statement` from a wave-8 surface whose digit fields are
supplied in pure carry-trajectory form. -/
theorem erdos260_of_trajectoryDigits (base : Erdos260PushResidual)
    (S : ReturnDigitTrajectorySurface) : Erdos260Statement :=
  erdos260_of_pushResidual (pushResidual_withTrajectoryDigits base S)

/-- **Strength accounting** (no strength hidden modulo deepness): any wave-8 provider
yields the trajectory surface, GIVEN fibre deepness at every ctx (`OlcFibreDeep`; only
positions `0,1,2` escape the deep escape bound).  The `returnMaxClean` lane needs no
deepness. -/
def trajectorySurface_of_pushResidual (R : Erdos260PushResidual)
    (hdeep : ∀ ctx : ActualFailureContext, OlcFibreDeep ctx) :
    ReturnDigitTrajectorySurface where
  returnZeroTrajectory := fun ctx h1 h2 h3 h4 =>
    (returnZeroBody_iff_belowBandTrajectory ctx (hdeep ctx)).1
      (returnZeroBody_of_banded ctx (R.returnZero ctx h1 h2 h3 h4))
  returnMaxCleanTrajectory := fun ctx h1 h2 =>
    (returnMaxCleanBody_iff_carryTrajectory ctx).1
      (returnMaxCleanBody_of_banded ctx (R.returnMaxClean ctx h1 h2))

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the banded digit closure module. -/
def bandedDigitClosureStatus : List String :=
  [ "ESCAPE-TIME ARGUMENT (closed, exact): band_zeroRun_envelope - from a band-carry " ++
      "position N (Q*(N+1) <= 2*R_N, the exact ReturnZeroBodyBanded demand condition, " ++
      "bandedDemand_band_iff) a zero run of length h on (N, N+h] forces " ++
      "2^h*(N+1) <= 2*(N+h+2) (doubling integerCarry_add_of_zero_digits vs the upper " ++
      "envelope integerCarry_bounds_of_rational_value, sharper than the Q*(N+h+3) " ++
      "guess).  Corollaries: band_zeroRun_le_three (h <= 3 at EVERY N), " ++
      "band_zeroRun_le_one_of_deep (h <= 1 for N >= 3), band_zeroRun_le_bandEscapeH " ++
      "with the explicit H(N) = bandEscapeH N (3 at N=0; 2 at N=1,2; 1 from N=3 on).  " ++
      "So consecutive zero demands push the carry out of the band in at most 3 steps " ++
      "- not ~log2(N): the band is so narrow relative to the doubling that escape is " ++
      "essentially immediate.",
    "THE COLLAPSE (digit fields -> pure carry trajectory, the honest iff): " ++
      "zeroRun_iff_belowBand_trajectory (x >= 3): zeros on (x,z] IFF strictly below " ++
      "band (2R_N < Q*(N+1), StrictlyBelowBand) at every N in [x, z-2] AND the final " ++
      "step doubles (carryOf z = 2*carryOf (z-1)).  HONEST CORRECTION to the proposed " ++
      "'returnZeroBanded iff strictly-below-band on ALL demanded intervals': FALSE at " ++
      "the final position - the carry at z-1 may sit INSIDE the band [Q*z, Q*(z+2)] " ++
      "with d z = 0 still consistent (carry_upper_of_digit_zero only confines from " ++
      "above); the final step survives as a carry-doubling equation, which is still " ++
      "pure carry (digit_zero_iff_carry_doubles), so ZERO digit content remains.  " ++
      "Unconditional variant zeroRun_iff_belowBand_trajectory_uncond (no x >= 3): " ++
      "below band on [x, z-4] plus clean tail doubling over the last <= 3 steps.",
    "BODY-LEVEL RESTATEMENTS (exact names): returnZeroBody_iff_cleanDoubling " ++
      "(UNCONDITIONAL - ReturnZeroBody iff ReturnZeroCleanDoubling, every demanded " ++
      "slice interval doubles cleanly carryOf z = 2^(z-x)*carryOf x, via " ++
      "cleanReturnSegment_iff_zeroRun); returnZeroBody_iff_belowBandTrajectory " ++
      "(ReturnZeroBody iff ReturnZeroBelowBandTrajectory under OlcFibreDeep - all " ++
      "fibre members >= 3; the reconstruction direction " ++
      "returnZeroBody_of_belowBandTrajectory is UNCONDITIONAL); " ++
      "returnMaxCleanBody_iff_carryTrajectory (UNCONDITIONAL - ReturnMaxCleanBody iff " ++
      "ReturnMaxCleanCarryTrajectory, carryOf (k+1) = 2*carryOf k at per-slice " ++
      "maxima); returnMaxCleanBody_of_belowBand (free at below-band maxima).",
    "BELOW-BAND TRAJECTORY BOUNDS (closed): belowBand_zeroRun (zeros come FREE on " ++
      "below-band runs); belowBand_pow_lt (2^(z-x) < Q*z on a strictly-below-band run " ++
      "[x,z) - the doubled POSITIVE carry must stay under the lower edge); " ++
      "belowBand_length_le_log (z-x <= Nat.log 2 (Q*z)); zeroRun_pow_le_envelope " ++
      "(2^(z-x) <= Q*(z+2) for ANY satisfiable zero demand, band or not); " ++
      "returnZeroBody_interval_le_log (demanded slice intervals are log-short); " ++
      "zeroRun_carry_confined / returnZeroBody_carry_confined (the high-band forcing " ++
      "as a recorded confinement constraint 2*R_{j-1} <= Q*(j+2)).",
    "RATIONAL-VALUE / ONSET AUDIT (the dangerous link CHECKED, in our favour): " ++
      "hrational AND hnonterm are FIELDS of every ActualFailureContext " ++
      "(UnconditionalTheorem.lean:90-101) - not only pinned contexts.  Hence " ++
      "carryOf_pos: R_N > 0 at EVERY index N (integerCarry_pos_of_not_eventuallyZero " ++
      "needs no onset; the dichotomy integerCarry_exists_zero_iff_eventuallyZero " ++
      "excludes R_N = 0 outright on non-terminating expansions).  The only " ++
      "onset-limited forcing in-tree is the parity one (t <= N), UNUSED here.  The " ++
      "numerator witness is unique (ctxNum_unique), so the forall-P quantification " ++
      "inside the banded bodies collapses to BandAtOrAbove (bandedDemand_band_iff).",
    "SLICE SPACING vs LOG-SHORT DEMAND (the honest NON-closure): sameSlice_gap_pow_le " ++
      "(2^(carryVal2 x) <= z - x via returnSelfRefKey_gapDiv); " ++
      "returnZeroBody_sameSlice_doubleExp (a satisfiable demand on a same-slice pair " ++
      "forces 2^(2^(carryVal2 x)) <= Q*(z+2)); " ++
      "returnZeroBody_refuted_of_sameSlice_doubleExp (the demand is REFUTED whenever " ++
      "Q*(z+2) < 2^(2^(carryVal2 x))).  WHY THIS DOES NOT CLOSE THE FIELDS OUTRIGHT: " ++
      "carryVal2 x can be 0 (odd carry - then the spacing bound is z-x >= 1, vacuous); " ++
      "no in-tree result gives a positive LOWER bound on carryVal2 at fibre members - " ++
      "the capstone returnZero guard even supplies the UPPER bound 2^(carryVal2 k) < " ++
      "(supportShell ...).card in the demanded regime.  So slices are NOT forced to " ++
      "be singletons; returnZero is NOT vacuous; both fields remain open, restated.",
    "DELIVERABLE (sharpest restatement + successor surface): " ++
      "ReturnDigitTrajectorySurface (the two digit fields in pure carry-trajectory " ++
      "form under the verbatim wave-8 guards); field bridges " ++
      "pushResidual_returnZero_field_of_trajectory / " ++
      "pushResidual_returnMaxClean_field_of_trajectory (exact capstone field shapes); " ++
      "combinator pushResidual_withTrajectoryDigits; endpoint " ++
      "erdos260_of_trajectoryDigits (base : Erdos260PushResidual) " ++
      "(S : ReturnDigitTrajectorySurface) : Erdos260Statement.  STRENGTH ACCOUNTING: " ++
      "trajectory => banded is UNCONDITIONAL (returnZeroBodyBanded_of_belowBand" ++
      "Trajectory / returnMaxCleanBodyBanded_of_carryTrajectory); the converse " ++
      "trajectorySurface_of_pushResidual needs OlcFibreDeep at every ctx (all fibre " ++
      "members >= 3, NOT proved in-tree - only positions 0,1,2 escape, with escape " ++
      "times 3,2,2); the returnMaxClean lane is equivalent with NO caveat.",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new axiom " ++
      "/ native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem bandedDigitClosureStatus_nonempty : bandedDigitClosureStatus ≠ [] := by
  simp [bandedDigitClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms bandAtOrAbove_of_not_strictlyBelowBand
#print axioms strictlyBelowBand_or_bandAtOrAbove
#print axioms carryOf_eq_integerCarry
#print axioms ctxNum_unique
#print axioms integerCarry_value_eq_carryOf
#print axioms bandedDemand_band_iff
#print axioms digit_zero_of_strictlyBelowBand
#print axioms band_zeroRun_envelope
#print axioms two_pow_gt_linear
#print axioms two_pow_ge_succ_succ
#print axioms band_zeroRun_le_three
#print axioms band_zeroRun_le_one_of_deep
#print axioms band_zeroRun_le_bandEscapeH
#print axioms belowBand_zeroRun
#print axioms belowBand_pow_lt
#print axioms belowBand_length_le_log
#print axioms zeroRun_belowBand_interior
#print axioms zeroRun_of_belowBand_trajectory
#print axioms zeroRun_iff_belowBand_trajectory
#print axioms zeroRun_iff_belowBand_trajectory_uncond
#print axioms zeroRun_pow_le_envelope
#print axioms zeroRun_carry_confined
#print axioms mem_olcFibre_of_mem_olcSlice
#print axioms key_eq_of_mem_olcSlice
#print axioms returnZeroBody_iff_cleanDoubling
#print axioms returnZeroBody_of_belowBandTrajectory
#print axioms returnZeroBody_iff_belowBandTrajectory
#print axioms returnMaxCleanBody_iff_carryTrajectory
#print axioms returnMaxCleanBody_of_belowBand
#print axioms sameSlice_gap_pow_le
#print axioms returnZeroBody_sameSlice_doubleExp
#print axioms returnZeroBody_refuted_of_sameSlice_doubleExp
#print axioms returnZeroBody_interval_le_log
#print axioms returnZeroBody_carry_confined
#print axioms returnZeroBodyBanded_of_belowBandTrajectory
#print axioms returnMaxCleanBodyBanded_of_carryTrajectory
#print axioms pushResidual_returnZero_field_of_trajectory
#print axioms pushResidual_returnMaxClean_field_of_trajectory
#print axioms pushResidual_withTrajectoryDigits
#print axioms erdos260_of_trajectoryDigits
#print axioms trajectorySurface_of_pushResidual
#print axioms bandedDigitClosureStatus_nonempty

end

end Erdos260
