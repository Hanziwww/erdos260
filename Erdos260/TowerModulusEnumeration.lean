import Erdos260.TowerFixedPointClosure

/-!
# Tower / Class 2, wave 5 - the modulus enumeration `25 <= q < 105`

This module (NEW; it edits no existing file) executes the extension path recorded by
`TowerFixedPointClosure`: the un-enumerated odd moduli `25 <= q != 105` of the escape
surface `TowerEscape` each carry a FINITE pin-admissible `K0` list (the divisor pin
`2*K0 + 1 | q`, `class1SlopeDatum_pin`) and an explicit orbit table.  We enumerate ALL
forty odd moduli `q in {25, 27, ..., 103}` (the class-2-relevant window: a nonempty
class-2 fibre needs `9 <= q` and `q <= 15` or `25 <= q`,
`modulus_window_of_class2Fibre_nonempty`), prove the per-`(q, K0)` cycle data, and shrink
the residual.

## What is proved here

1. **Forty pin enumerations** (`towerME_pin_*`): for every odd `25 <= q <= 103` the
   admissible base numerators `K0` (those with `2*K0 + 1 | q`) are listed exactly;
   the kernel checks the divisor scan (`decide`, NOT `native_decide`).
2. **46 band-4-free data** (`towerME_empty_*`): the recurrent cycle avoids band 4,
   so the routed class-2 fibre is EMPTY outright and the cycle inequality holds at
   every sparsity block (via `class2Fibre_empty_of_collision_free` /
   `class2CycleInequality_of_collision_free`).
3. **10 whole moduli close completely** (`towerME_empty_mod_*`): on
   `q in {27, 31, 33, 43, 45, 51, 65, 85, 91, 93}` EVERY admissible `K0` rides a band-4-free
   cycle - the class-2 fibre of every such shell is empty, with no residual demand.
4. **44 counted data** (`towerME_ineq_*`): the cycle meets band 4 (`b4 >= 1` per
   period `c`), and the cycle inequality `m0 * (b4 * ceil(K/c)) <= K` is closed for
   every sparsity block `m0 <= t` at the explicit per-pair threshold `t` - the width
   escalation `64*m0 <= 3*(r+1) + 63 <= 3*K + 63` (`towerMEWidth_le`) feeds the exact
   rounding `towerCycleRounding` through ONE reusable numeric splitter
   (`towerME_numeric`), whose per-level checks are kernel-verified (`decide`).
5. **The high-band-4-density hard core is ONE pair** (`towerME_hard_63_10`): `(63, 10)`
   rides the period-2 cycle `17 -> 5` with gaps `2, 4` - band-4 density `1/2`, so the
   demanded density `1/m0 <= 1/2` for every deep shell (`m0 >= 2`) and cycle counting
   closes NOTHING.  `(63, 10)` joins the fixed pairs `(15,1), (15,2), (105,7)` as the
   hard core; its pinned datum has `oddpart(Q)*21 = 63` (so `oddpart(Q) = 3`).
6. **The strictly smaller successor residual + the exact capstone bridge**:
   `TowerModulusEnumerationResidual` demands the cycle inequality only on
   `TowerModulusEnumEscape` (the wave-4 families `q in {9, 11, 13}` above their
   thresholds, the fixed pairs at `q in {15, 105}`, the enumerated counted pairs ABOVE
   their per-pair thresholds (`towerEnumHardTriples`), the hard pair `(63, 10)`, and
   the un-enumerated odd moduli `107 <= q`).
   `towerFixedPointResidual_of_modulusEnumeration` rebuilds the wave-4 residual;
   `towerSplit_of_modulusEnumeration` rebuilds the capstone `towerSplit` field
   VERBATIM (through `towerSplit_of_fixedPointResidual`);
   `towerCountBound_of_modulusEnumeration` discharges `Class2DeepShellCountBound`;
   `towerModulusEnumerationResidual_of_fixedPointResidual` witnesses that the new
   residual is no stronger than the wave-4 one.

## Honesty - what is NOT closed

* The counted families keep their escape regimes `m0 >= t + 1` (each `1/m0` falls
  below the cycle density `b4/c` there, exactly as for `q in {9, 11, 13}` and
  `(105, 52)` in wave 4).
* `(63, 10)` is recorded, characterized, and NOT closed (density `1/2`).
* The odd moduli `107 <= q` remain un-enumerated (same mechanical method applies).

No `sorry`, `admit`, `axiom`, or `native_decide`.  No degenerate witnesses: every
theorem is about the genuine `class1SlopeDatum` of the actual failing-shell context
and the genuine routed class-2 fibre; the orbit tables are explicit E.13 step
evaluations checked against the canonical band bounds.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 1.  The sparsity-block width floor and the reusable numeric splitter -/

/-- The width floor at sparsity block `u`: every deep shell (`K >= 22`) with
`towerSparsityBlock = u` has `shellWidth >= max 22 ((64*u - 61) / 3)` (the order pin
`m0 = (3*(r+1) + 63) / 64` inverted, `ceil((64*u - 63)/3) = (64*u - 61)/3`). -/
def towerMEWidth (u : ℕ) : ℕ := max 22 ((64 * u - 61) / 3)

/-- **The width floor holds at the actual block**: `towerMEWidth m0 <= K` on every shell
with `K >= 22`. -/
theorem towerMEWidth_le (ctx : ActualFailureContext) (hK : 22 ≤ shellWidth ctx) :
    towerMEWidth (towerSparsityBlock ctx) ≤ shellWidth ctx := by
  have hdef : towerSparsityBlock ctx = (3 * (ctx.n24CarryData.r + 1) + 63) / 64 := rfl
  have hKr := r_add_one_le_width ctx
  unfold towerMEWidth
  omega

/-- **The reusable numeric splitter**: per-level kernel checks
`u * b * (towerMEWidth u + c - 1) <= towerMEWidth u * c` for all `u <= t`, plus the
strict-density guard `t * b < c`, discharge the cycle-inequality numeric side
`m0 * b * (K + c - 1) <= K * c` on every shell with `m0 <= t` and `K >= 22` - the
monotone interpolation between the level floor and the actual width loses nothing. -/
theorem towerME_numeric (ctx : ActualFailureContext) {b c t : ℕ}
    (hc : 1 ≤ c)
    (hm : towerSparsityBlock ctx ≤ t)
    (hK : 22 ≤ shellWidth ctx)
    (hmono : t * b + 1 ≤ c)
    (hcheck : ∀ u < t + 1,
      u * b * (towerMEWidth u + c - 1) ≤ towerMEWidth u * c) :
    towerSparsityBlock ctx * b * (shellWidth ctx + c - 1) ≤ shellWidth ctx * c := by
  have hWK : towerMEWidth (towerSparsityBlock ctx) ≤ shellWidth ctx :=
    towerMEWidth_le ctx hK
  have hW22 : 22 ≤ towerMEWidth (towerSparsityBlock ctx) := by
    unfold towerMEWidth
    omega
  have h1 : towerSparsityBlock ctx * b
        * (towerMEWidth (towerSparsityBlock ctx) + c - 1)
      ≤ towerMEWidth (towerSparsityBlock ctx) * c :=
    hcheck (towerSparsityBlock ctx) (by omega)
  have hmb : towerSparsityBlock ctx * b ≤ c - 1 := by
    have h := Nat.mul_le_mul_right b hm
    omega
  obtain ⟨D, hD⟩ : ∃ D, shellWidth ctx = towerMEWidth (towerSparsityBlock ctx) + D :=
    ⟨shellWidth ctx - towerMEWidth (towerSparsityBlock ctx), by omega⟩
  have h2 : towerSparsityBlock ctx * b * D ≤ (c - 1) * D :=
    Nat.mul_le_mul_right D hmb
  have h3 : (c - 1) * D ≤ D * c := by
    calc (c - 1) * D ≤ c * D := Nat.mul_le_mul_right D (by omega)
      _ = D * c := Nat.mul_comm c D
  have hsplit : shellWidth ctx + c - 1
      = (towerMEWidth (towerSparsityBlock ctx) + c - 1) + D := by
    omega
  calc towerSparsityBlock ctx * b * (shellWidth ctx + c - 1)
      = towerSparsityBlock ctx * b
          * ((towerMEWidth (towerSparsityBlock ctx) + c - 1) + D) := by
        rw [hsplit]
    _ = towerSparsityBlock ctx * b * (towerMEWidth (towerSparsityBlock ctx) + c - 1)
          + towerSparsityBlock ctx * b * D := Nat.mul_add _ _ _
    _ ≤ towerMEWidth (towerSparsityBlock ctx) * c + (c - 1) * D :=
        Nat.add_le_add h1 h2
    _ ≤ towerMEWidth (towerSparsityBlock ctx) * c + D * c :=
        Nat.add_le_add_left h3 _
    _ = (towerMEWidth (towerSparsityBlock ctx) + D) * c := (Nat.add_mul _ _ _).symm
    _ = shellWidth ctx * c := by rw [← hD]

/-! ## Part 2.  The forty pin enumerations `25 <= q <= 103`

Each odd modulus carries the divisor pin `2*K0 + 1 | q`; the kernel scans the finite
range `1 <= K0 < (q+1)/2` (`decide` - plain kernel reduction, NOT `native_decide`). -/

private theorem towerME_pin_dec_25 : ∀ v < 13, 1 ≤ v → (2 * v + 1 ∣ 25) →
    (v = 2 ∨ v = 12) := by decide

/-- `q = 25` pins the base numerator into `{2, 12}` (divisors `5, 25`). -/
theorem towerME_pin_25 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) :
    (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 12 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 13 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_25 _ hub hpos hdvd

private theorem towerME_pin_dec_27 : ∀ v < 14, 1 ≤ v → (2 * v + 1 ∣ 27) →
    (v = 1 ∨ v = 4 ∨ v = 13) := by decide

/-- `q = 27` pins the base numerator into `{1, 4, 13}` (divisors `3, 9, 27`). -/
theorem towerME_pin_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 4 ∨ (class1SlopeDatum ctx).K₀ = 13 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 14 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_27 _ hub hpos hdvd

private theorem towerME_pin_dec_29 : ∀ v < 15, 1 ≤ v → (2 * v + 1 ∣ 29) →
    (v = 14) := by decide

/-- `q = 29` pins the base numerator into `{14}` (divisors `29`). -/
theorem towerME_pin_29 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) :
    (class1SlopeDatum ctx).K₀ = 14 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 15 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_29 _ hub hpos hdvd

private theorem towerME_pin_dec_31 : ∀ v < 16, 1 ≤ v → (2 * v + 1 ∣ 31) →
    (v = 15) := by decide

/-- `q = 31` pins the base numerator into `{15}` (divisors `31`). -/
theorem towerME_pin_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) :
    (class1SlopeDatum ctx).K₀ = 15 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 16 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_31 _ hub hpos hdvd

private theorem towerME_pin_dec_33 : ∀ v < 17, 1 ≤ v → (2 * v + 1 ∣ 33) →
    (v = 1 ∨ v = 5 ∨ v = 16) := by decide

/-- `q = 33` pins the base numerator into `{1, 5, 16}` (divisors `3, 11, 33`). -/
theorem towerME_pin_33 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 5 ∨ (class1SlopeDatum ctx).K₀ = 16 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 17 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_33 _ hub hpos hdvd

private theorem towerME_pin_dec_35 : ∀ v < 18, 1 ≤ v → (2 * v + 1 ∣ 35) →
    (v = 2 ∨ v = 3 ∨ v = 17) := by decide

/-- `q = 35` pins the base numerator into `{2, 3, 17}` (divisors `5, 7, 35`). -/
theorem towerME_pin_35 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) :
    (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 3 ∨ (class1SlopeDatum ctx).K₀ = 17 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 18 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_35 _ hub hpos hdvd

private theorem towerME_pin_dec_37 : ∀ v < 19, 1 ≤ v → (2 * v + 1 ∣ 37) →
    (v = 18) := by decide

/-- `q = 37` pins the base numerator into `{18}` (divisors `37`). -/
theorem towerME_pin_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) :
    (class1SlopeDatum ctx).K₀ = 18 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 19 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_37 _ hub hpos hdvd

private theorem towerME_pin_dec_39 : ∀ v < 20, 1 ≤ v → (2 * v + 1 ∣ 39) →
    (v = 1 ∨ v = 6 ∨ v = 19) := by decide

/-- `q = 39` pins the base numerator into `{1, 6, 19}` (divisors `3, 13, 39`). -/
theorem towerME_pin_39 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 6 ∨ (class1SlopeDatum ctx).K₀ = 19 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 20 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_39 _ hub hpos hdvd

private theorem towerME_pin_dec_41 : ∀ v < 21, 1 ≤ v → (2 * v + 1 ∣ 41) →
    (v = 20) := by decide

/-- `q = 41` pins the base numerator into `{20}` (divisors `41`). -/
theorem towerME_pin_41 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) :
    (class1SlopeDatum ctx).K₀ = 20 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 21 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_41 _ hub hpos hdvd

private theorem towerME_pin_dec_43 : ∀ v < 22, 1 ≤ v → (2 * v + 1 ∣ 43) →
    (v = 21) := by decide

/-- `q = 43` pins the base numerator into `{21}` (divisors `43`). -/
theorem towerME_pin_43 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) :
    (class1SlopeDatum ctx).K₀ = 21 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 22 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_43 _ hub hpos hdvd

private theorem towerME_pin_dec_45 : ∀ v < 23, 1 ≤ v → (2 * v + 1 ∣ 45) →
    (v = 1 ∨ v = 2 ∨ v = 4 ∨ v = 7 ∨ v = 22) := by decide

/-- `q = 45` pins the base numerator into `{1, 2, 4, 7, 22}` (divisors `3, 5, 9, 15, 45`). -/
theorem towerME_pin_45 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 4 ∨ (class1SlopeDatum ctx).K₀ = 7 ∨ (class1SlopeDatum ctx).K₀ = 22 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 23 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_45 _ hub hpos hdvd

private theorem towerME_pin_dec_47 : ∀ v < 24, 1 ≤ v → (2 * v + 1 ∣ 47) →
    (v = 23) := by decide

/-- `q = 47` pins the base numerator into `{23}` (divisors `47`). -/
theorem towerME_pin_47 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) :
    (class1SlopeDatum ctx).K₀ = 23 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 24 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_47 _ hub hpos hdvd

private theorem towerME_pin_dec_49 : ∀ v < 25, 1 ≤ v → (2 * v + 1 ∣ 49) →
    (v = 3 ∨ v = 24) := by decide

/-- `q = 49` pins the base numerator into `{3, 24}` (divisors `7, 49`). -/
theorem towerME_pin_49 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) :
    (class1SlopeDatum ctx).K₀ = 3 ∨ (class1SlopeDatum ctx).K₀ = 24 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 25 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_49 _ hub hpos hdvd

private theorem towerME_pin_dec_51 : ∀ v < 26, 1 ≤ v → (2 * v + 1 ∣ 51) →
    (v = 1 ∨ v = 8 ∨ v = 25) := by decide

/-- `q = 51` pins the base numerator into `{1, 8, 25}` (divisors `3, 17, 51`). -/
theorem towerME_pin_51 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 8 ∨ (class1SlopeDatum ctx).K₀ = 25 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 26 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_51 _ hub hpos hdvd

private theorem towerME_pin_dec_53 : ∀ v < 27, 1 ≤ v → (2 * v + 1 ∣ 53) →
    (v = 26) := by decide

/-- `q = 53` pins the base numerator into `{26}` (divisors `53`). -/
theorem towerME_pin_53 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 53) :
    (class1SlopeDatum ctx).K₀ = 26 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 27 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_53 _ hub hpos hdvd

private theorem towerME_pin_dec_55 : ∀ v < 28, 1 ≤ v → (2 * v + 1 ∣ 55) →
    (v = 2 ∨ v = 5 ∨ v = 27) := by decide

/-- `q = 55` pins the base numerator into `{2, 5, 27}` (divisors `5, 11, 55`). -/
theorem towerME_pin_55 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) :
    (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 5 ∨ (class1SlopeDatum ctx).K₀ = 27 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 28 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_55 _ hub hpos hdvd

private theorem towerME_pin_dec_57 : ∀ v < 29, 1 ≤ v → (2 * v + 1 ∣ 57) →
    (v = 1 ∨ v = 9 ∨ v = 28) := by decide

/-- `q = 57` pins the base numerator into `{1, 9, 28}` (divisors `3, 19, 57`). -/
theorem towerME_pin_57 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 9 ∨ (class1SlopeDatum ctx).K₀ = 28 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 29 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_57 _ hub hpos hdvd

private theorem towerME_pin_dec_59 : ∀ v < 30, 1 ≤ v → (2 * v + 1 ∣ 59) →
    (v = 29) := by decide

/-- `q = 59` pins the base numerator into `{29}` (divisors `59`). -/
theorem towerME_pin_59 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 59) :
    (class1SlopeDatum ctx).K₀ = 29 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 30 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_59 _ hub hpos hdvd

private theorem towerME_pin_dec_61 : ∀ v < 31, 1 ≤ v → (2 * v + 1 ∣ 61) →
    (v = 30) := by decide

/-- `q = 61` pins the base numerator into `{30}` (divisors `61`). -/
theorem towerME_pin_61 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 61) :
    (class1SlopeDatum ctx).K₀ = 30 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 31 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_61 _ hub hpos hdvd

private theorem towerME_pin_dec_63 : ∀ v < 32, 1 ≤ v → (2 * v + 1 ∣ 63) →
    (v = 1 ∨ v = 3 ∨ v = 4 ∨ v = 10 ∨ v = 31) := by decide

/-- `q = 63` pins the base numerator into `{1, 3, 4, 10, 31}` (divisors `3, 7, 9, 21, 63`). -/
theorem towerME_pin_63 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 3 ∨ (class1SlopeDatum ctx).K₀ = 4 ∨ (class1SlopeDatum ctx).K₀ = 10 ∨ (class1SlopeDatum ctx).K₀ = 31 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 32 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_63 _ hub hpos hdvd

private theorem towerME_pin_dec_65 : ∀ v < 33, 1 ≤ v → (2 * v + 1 ∣ 65) →
    (v = 2 ∨ v = 6 ∨ v = 32) := by decide

/-- `q = 65` pins the base numerator into `{2, 6, 32}` (divisors `5, 13, 65`). -/
theorem towerME_pin_65 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) :
    (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 6 ∨ (class1SlopeDatum ctx).K₀ = 32 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 33 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_65 _ hub hpos hdvd

private theorem towerME_pin_dec_67 : ∀ v < 34, 1 ≤ v → (2 * v + 1 ∣ 67) →
    (v = 33) := by decide

/-- `q = 67` pins the base numerator into `{33}` (divisors `67`). -/
theorem towerME_pin_67 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 67) :
    (class1SlopeDatum ctx).K₀ = 33 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 34 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_67 _ hub hpos hdvd

private theorem towerME_pin_dec_69 : ∀ v < 35, 1 ≤ v → (2 * v + 1 ∣ 69) →
    (v = 1 ∨ v = 11 ∨ v = 34) := by decide

/-- `q = 69` pins the base numerator into `{1, 11, 34}` (divisors `3, 23, 69`). -/
theorem towerME_pin_69 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 11 ∨ (class1SlopeDatum ctx).K₀ = 34 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 35 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_69 _ hub hpos hdvd

private theorem towerME_pin_dec_71 : ∀ v < 36, 1 ≤ v → (2 * v + 1 ∣ 71) →
    (v = 35) := by decide

/-- `q = 71` pins the base numerator into `{35}` (divisors `71`). -/
theorem towerME_pin_71 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 71) :
    (class1SlopeDatum ctx).K₀ = 35 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 36 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_71 _ hub hpos hdvd

private theorem towerME_pin_dec_73 : ∀ v < 37, 1 ≤ v → (2 * v + 1 ∣ 73) →
    (v = 36) := by decide

/-- `q = 73` pins the base numerator into `{36}` (divisors `73`). -/
theorem towerME_pin_73 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 73) :
    (class1SlopeDatum ctx).K₀ = 36 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 37 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_73 _ hub hpos hdvd

private theorem towerME_pin_dec_75 : ∀ v < 38, 1 ≤ v → (2 * v + 1 ∣ 75) →
    (v = 1 ∨ v = 2 ∨ v = 7 ∨ v = 12 ∨ v = 37) := by decide

/-- `q = 75` pins the base numerator into `{1, 2, 7, 12, 37}` (divisors `3, 5, 15, 25, 75`). -/
theorem towerME_pin_75 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 7 ∨ (class1SlopeDatum ctx).K₀ = 12 ∨ (class1SlopeDatum ctx).K₀ = 37 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 38 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_75 _ hub hpos hdvd

private theorem towerME_pin_dec_77 : ∀ v < 39, 1 ≤ v → (2 * v + 1 ∣ 77) →
    (v = 3 ∨ v = 5 ∨ v = 38) := by decide

/-- `q = 77` pins the base numerator into `{3, 5, 38}` (divisors `7, 11, 77`). -/
theorem towerME_pin_77 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 77) :
    (class1SlopeDatum ctx).K₀ = 3 ∨ (class1SlopeDatum ctx).K₀ = 5 ∨ (class1SlopeDatum ctx).K₀ = 38 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 39 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_77 _ hub hpos hdvd

private theorem towerME_pin_dec_79 : ∀ v < 40, 1 ≤ v → (2 * v + 1 ∣ 79) →
    (v = 39) := by decide

/-- `q = 79` pins the base numerator into `{39}` (divisors `79`). -/
theorem towerME_pin_79 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 79) :
    (class1SlopeDatum ctx).K₀ = 39 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 40 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_79 _ hub hpos hdvd

private theorem towerME_pin_dec_81 : ∀ v < 41, 1 ≤ v → (2 * v + 1 ∣ 81) →
    (v = 1 ∨ v = 4 ∨ v = 13 ∨ v = 40) := by decide

/-- `q = 81` pins the base numerator into `{1, 4, 13, 40}` (divisors `3, 9, 27, 81`). -/
theorem towerME_pin_81 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 81) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 4 ∨ (class1SlopeDatum ctx).K₀ = 13 ∨ (class1SlopeDatum ctx).K₀ = 40 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 41 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_81 _ hub hpos hdvd

private theorem towerME_pin_dec_83 : ∀ v < 42, 1 ≤ v → (2 * v + 1 ∣ 83) →
    (v = 41) := by decide

/-- `q = 83` pins the base numerator into `{41}` (divisors `83`). -/
theorem towerME_pin_83 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 83) :
    (class1SlopeDatum ctx).K₀ = 41 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 42 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_83 _ hub hpos hdvd

private theorem towerME_pin_dec_85 : ∀ v < 43, 1 ≤ v → (2 * v + 1 ∣ 85) →
    (v = 2 ∨ v = 8 ∨ v = 42) := by decide

/-- `q = 85` pins the base numerator into `{2, 8, 42}` (divisors `5, 17, 85`). -/
theorem towerME_pin_85 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) :
    (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 8 ∨ (class1SlopeDatum ctx).K₀ = 42 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 43 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_85 _ hub hpos hdvd

private theorem towerME_pin_dec_87 : ∀ v < 44, 1 ≤ v → (2 * v + 1 ∣ 87) →
    (v = 1 ∨ v = 14 ∨ v = 43) := by decide

/-- `q = 87` pins the base numerator into `{1, 14, 43}` (divisors `3, 29, 87`). -/
theorem towerME_pin_87 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 14 ∨ (class1SlopeDatum ctx).K₀ = 43 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 44 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_87 _ hub hpos hdvd

private theorem towerME_pin_dec_89 : ∀ v < 45, 1 ≤ v → (2 * v + 1 ∣ 89) →
    (v = 44) := by decide

/-- `q = 89` pins the base numerator into `{44}` (divisors `89`). -/
theorem towerME_pin_89 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 89) :
    (class1SlopeDatum ctx).K₀ = 44 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 45 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_89 _ hub hpos hdvd

private theorem towerME_pin_dec_91 : ∀ v < 46, 1 ≤ v → (2 * v + 1 ∣ 91) →
    (v = 3 ∨ v = 6 ∨ v = 45) := by decide

/-- `q = 91` pins the base numerator into `{3, 6, 45}` (divisors `7, 13, 91`). -/
theorem towerME_pin_91 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) :
    (class1SlopeDatum ctx).K₀ = 3 ∨ (class1SlopeDatum ctx).K₀ = 6 ∨ (class1SlopeDatum ctx).K₀ = 45 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 46 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_91 _ hub hpos hdvd

private theorem towerME_pin_dec_93 : ∀ v < 47, 1 ≤ v → (2 * v + 1 ∣ 93) →
    (v = 1 ∨ v = 15 ∨ v = 46) := by decide

/-- `q = 93` pins the base numerator into `{1, 15, 46}` (divisors `3, 31, 93`). -/
theorem towerME_pin_93 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 15 ∨ (class1SlopeDatum ctx).K₀ = 46 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 47 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_93 _ hub hpos hdvd

private theorem towerME_pin_dec_95 : ∀ v < 48, 1 ≤ v → (2 * v + 1 ∣ 95) →
    (v = 2 ∨ v = 9 ∨ v = 47) := by decide

/-- `q = 95` pins the base numerator into `{2, 9, 47}` (divisors `5, 19, 95`). -/
theorem towerME_pin_95 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 95) :
    (class1SlopeDatum ctx).K₀ = 2 ∨ (class1SlopeDatum ctx).K₀ = 9 ∨ (class1SlopeDatum ctx).K₀ = 47 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 48 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_95 _ hub hpos hdvd

private theorem towerME_pin_dec_97 : ∀ v < 49, 1 ≤ v → (2 * v + 1 ∣ 97) →
    (v = 48) := by decide

/-- `q = 97` pins the base numerator into `{48}` (divisors `97`). -/
theorem towerME_pin_97 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 97) :
    (class1SlopeDatum ctx).K₀ = 48 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 49 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_97 _ hub hpos hdvd

private theorem towerME_pin_dec_99 : ∀ v < 50, 1 ≤ v → (2 * v + 1 ∣ 99) →
    (v = 1 ∨ v = 4 ∨ v = 5 ∨ v = 16 ∨ v = 49) := by decide

/-- `q = 99` pins the base numerator into `{1, 4, 5, 16, 49}` (divisors `3, 9, 11, 33, 99`). -/
theorem towerME_pin_99 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 4 ∨ (class1SlopeDatum ctx).K₀ = 5 ∨ (class1SlopeDatum ctx).K₀ = 16 ∨ (class1SlopeDatum ctx).K₀ = 49 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 50 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_99 _ hub hpos hdvd

private theorem towerME_pin_dec_101 : ∀ v < 51, 1 ≤ v → (2 * v + 1 ∣ 101) →
    (v = 50) := by decide

/-- `q = 101` pins the base numerator into `{50}` (divisors `101`). -/
theorem towerME_pin_101 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 101) :
    (class1SlopeDatum ctx).K₀ = 50 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 51 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_101 _ hub hpos hdvd

private theorem towerME_pin_dec_103 : ∀ v < 52, 1 ≤ v → (2 * v + 1 ∣ 103) →
    (v = 51) := by decide

/-- `q = 103` pins the base numerator into `{51}` (divisors `103`). -/
theorem towerME_pin_103 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 103) :
    (class1SlopeDatum ctx).K₀ = 51 := by
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq] at hdvd
  have hpos : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  have hub : (class1SlopeDatum ctx).K₀ < 52 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact towerME_pin_dec_103 _ hub hpos hdvd

/-! ## Part 3.  The explicit orbit tables (E.13 step evaluations) -/

/-- Orbit cycle for `(25, 2)`: `7 -> 3 -> 23 -> 21 -> 17 -> 9 -> 11 -> 19 -> 13 -> 1`, canonical gaps
`2, 4, 1, 1, 1, 2, 2, 1, 1, 5` - period `10`, band-4 count `1` (positions `{2}`). -/
private theorem towerME_cyc_25_2 :
    slopeOrbit 25 2 (1 + 10) = slopeOrbit 25 2 1
      ∧ towerBand4CycleCount 25 2 10 ≤ 1 := by
  have e0 : slopeOrbit 25 2 0 = 2 := rfl
  have e1 : slopeOrbit 25 2 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 2 2 = 3 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 2 3 = 23 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 2 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 2 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 2 6 = 9 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 2 7 = 11 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 2 8 = 19 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 2 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 2 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 2 11 = 7 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 25 2 11 = slopeOrbit 25 2 1
    rw [e11, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 10).filter
        (fun j => canonGap 25 (slopeOrbit 25 2 j) = 4) ⊆ {2} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 2
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(25, 12)`: `23 -> 21 -> 17 -> 9 -> 11 -> 19 -> 13 -> 1 -> 7 -> 3`, canonical gaps
`1, 1, 1, 2, 2, 1, 1, 5, 2, 4` - period `10`, band-4 count `1` (positions `{10}`). -/
private theorem towerME_cyc_25_12 :
    slopeOrbit 25 12 (1 + 10) = slopeOrbit 25 12 1
      ∧ towerBand4CycleCount 25 12 10 ≤ 1 := by
  have e0 : slopeOrbit 25 12 0 = 12 := rfl
  have e1 : slopeOrbit 25 12 1 = 23 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 12 2 = 21 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 12 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 12 4 = 9 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 12 5 = 11 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 12 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 12 7 = 13 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 12 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 12 9 = 7 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 12 10 = 3 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 12 11 = 23 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 25 12 11 = slopeOrbit 25 12 1
    rw [e11, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 10).filter
        (fun j => canonGap 25 (slopeOrbit 25 12 j) = 4) ⊆ {10} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 10
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(27, 1)`: `5 -> 13 -> 25 -> 23 -> 19 -> 11 -> 17 -> 7 -> 1`, canonical gaps
`3, 2, 1, 1, 1, 2, 1, 2, 5` - period `9`, band-4-FREE. -/
private theorem towerME_cyc_27_1 :
    slopeOrbit 27 1 (1 + 9) = slopeOrbit 27 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 27 (slopeOrbit 27 1 j) ≠ 4 := by
  have e0 : slopeOrbit 27 1 0 = 1 := rfl
  have e1 : slopeOrbit 27 1 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 1 2 = 13 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 1 3 = 25 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 1 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 1 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 1 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 1 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 1 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 1 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 1 10 = 5 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 1 10 = slopeOrbit 27 1 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(27, 4)`: `5 -> 13 -> 25 -> 23 -> 19 -> 11 -> 17 -> 7 -> 1`, canonical gaps
`3, 2, 1, 1, 1, 2, 1, 2, 5` - period `9`, band-4-FREE. -/
private theorem towerME_cyc_27_4 :
    slopeOrbit 27 4 (1 + 9) = slopeOrbit 27 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 27 (slopeOrbit 27 4 j) ≠ 4 := by
  have e0 : slopeOrbit 27 4 0 = 4 := rfl
  have e1 : slopeOrbit 27 4 1 = 5 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 4 2 = 13 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 4 3 = 25 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 4 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 4 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 4 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 4 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 4 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 4 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 4 10 = 5 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 4 10 = slopeOrbit 27 4 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(27, 13)`: `25 -> 23 -> 19 -> 11 -> 17 -> 7 -> 1 -> 5 -> 13`, canonical gaps
`1, 1, 1, 2, 1, 2, 5, 3, 2` - period `9`, band-4-FREE. -/
private theorem towerME_cyc_27_13 :
    slopeOrbit 27 13 (1 + 9) = slopeOrbit 27 13 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 27 (slopeOrbit 27 13 j) ≠ 4 := by
  have e0 : slopeOrbit 27 13 0 = 13 := rfl
  have e1 : slopeOrbit 27 13 1 = 25 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 13 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 13 3 = 19 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 13 4 = 11 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 13 5 = 17 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 13 6 = 7 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 13 7 = 1 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 13 8 = 5 :=
    slopeOrbit_step_eval 7 4 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 13 9 = 13 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 13 10 = 25 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 13 10 = slopeOrbit 27 13 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(29, 14)`: `27 -> 25 -> 21 -> 13 -> 23 -> 17 -> 5 -> 11 -> 15 -> 1 -> 3 -> 19 -> 9 -> 7`, canonical gaps
`1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4, 1, 2, 3` - period `14`, band-4 count `1` (positions `{11}`). -/
private theorem towerME_cyc_29_14 :
    slopeOrbit 29 14 (1 + 14) = slopeOrbit 29 14 1
      ∧ towerBand4CycleCount 29 14 14 ≤ 1 := by
  have e0 : slopeOrbit 29 14 0 = 14 := rfl
  have e1 : slopeOrbit 29 14 1 = 27 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 29 14 2 = 25 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 29 14 3 = 21 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 29 14 4 = 13 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 29 14 5 = 23 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 29 14 6 = 17 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 29 14 7 = 5 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 29 14 8 = 11 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 29 14 9 = 15 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 29 14 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 29 14 11 = 3 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 29 14 12 = 19 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 29 14 13 = 9 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 29 14 14 = 7 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 29 14 15 = 27 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 29 14 15 = slopeOrbit 29 14 1
    rw [e15, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 14).filter
        (fun j => canonGap 29 (slopeOrbit 29 14 j) = 4) ⊆ {11} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 11
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(31, 15)`: `29 -> 27 -> 23 -> 15`, canonical gaps
`1, 1, 1, 2` - period `4`, band-4-FREE. -/
private theorem towerME_cyc_31_15 :
    slopeOrbit 31 15 (1 + 4) = slopeOrbit 31 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 31 (slopeOrbit 31 15 j) ≠ 4 := by
  have e0 : slopeOrbit 31 15 0 = 15 := rfl
  have e1 : slopeOrbit 31 15 1 = 29 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 15 2 = 27 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 31 15 3 = 23 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 31 15 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 31 15 5 = 29 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 15 5 = slopeOrbit 31 15 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(33, 1)`: `31 -> 29 -> 25 -> 17 -> 1`, canonical gaps
`1, 1, 1, 1, 6` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_33_1 :
    slopeOrbit 33 1 (1 + 5) = slopeOrbit 33 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 33 (slopeOrbit 33 1 j) ≠ 4 := by
  have e0 : slopeOrbit 33 1 0 = 1 := rfl
  have e1 : slopeOrbit 33 1 1 = 31 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 1 2 = 29 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 1 3 = 25 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 1 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 1 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 1 6 = 31 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 1 6 = slopeOrbit 33 1 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(33, 5)`: `7 -> 23 -> 13 -> 19 -> 5`, canonical gaps
`3, 1, 2, 1, 3` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_33_5 :
    slopeOrbit 33 5 (1 + 5) = slopeOrbit 33 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 33 (slopeOrbit 33 5 j) ≠ 4 := by
  have e0 : slopeOrbit 33 5 0 = 5 := rfl
  have e1 : slopeOrbit 33 5 1 = 7 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 5 2 = 23 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 5 3 = 13 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 5 4 = 19 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 5 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 5 6 = 7 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 5 6 = slopeOrbit 33 5 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(33, 16)`: `31 -> 29 -> 25 -> 17 -> 1`, canonical gaps
`1, 1, 1, 1, 6` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_33_16 :
    slopeOrbit 33 16 (1 + 5) = slopeOrbit 33 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 33 (slopeOrbit 33 16 j) ≠ 4 := by
  have e0 : slopeOrbit 33 16 0 = 16 := rfl
  have e1 : slopeOrbit 33 16 1 = 31 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 16 2 = 29 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 16 3 = 25 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 16 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 16 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 16 6 = 31 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 16 6 = slopeOrbit 33 16 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(35, 2)`: `29 -> 23 -> 11 -> 9 -> 1`, canonical gaps
`1, 1, 2, 2, 6` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_35_2 :
    slopeOrbit 35 2 (1 + 5) = slopeOrbit 35 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 35 (slopeOrbit 35 2 j) ≠ 4 := by
  have e0 : slopeOrbit 35 2 0 = 2 := rfl
  have e1 : slopeOrbit 35 2 1 = 29 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 2 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 2 3 = 11 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 2 4 = 9 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 2 5 = 1 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 2 6 = 29 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 35 2 6 = slopeOrbit 35 2 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(35, 3)`: `13 -> 17 -> 33 -> 31 -> 27 -> 19 -> 3`, canonical gaps
`2, 2, 1, 1, 1, 1, 4` - period `7`, band-4 count `1` (positions `{7}`). -/
private theorem towerME_cyc_35_3 :
    slopeOrbit 35 3 (1 + 7) = slopeOrbit 35 3 1
      ∧ towerBand4CycleCount 35 3 7 ≤ 1 := by
  have e0 : slopeOrbit 35 3 0 = 3 := rfl
  have e1 : slopeOrbit 35 3 1 = 13 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 3 2 = 17 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 3 3 = 33 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 3 4 = 31 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 3 5 = 27 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 3 6 = 19 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 35 3 7 = 3 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 35 3 8 = 13 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 35 3 8 = slopeOrbit 35 3 1
    rw [e8, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 35 (slopeOrbit 35 3 j) = 4) ⊆ {7} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 7
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(35, 17)`: `33 -> 31 -> 27 -> 19 -> 3 -> 13 -> 17`, canonical gaps
`1, 1, 1, 1, 4, 2, 2` - period `7`, band-4 count `1` (positions `{5}`). -/
private theorem towerME_cyc_35_17 :
    slopeOrbit 35 17 (1 + 7) = slopeOrbit 35 17 1
      ∧ towerBand4CycleCount 35 17 7 ≤ 1 := by
  have e0 : slopeOrbit 35 17 0 = 17 := rfl
  have e1 : slopeOrbit 35 17 1 = 33 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 17 2 = 31 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 17 3 = 27 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 17 4 = 19 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 17 5 = 3 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 17 6 = 13 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 35 17 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 35 17 8 = 33 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 35 17 8 = slopeOrbit 35 17 1
    rw [e8, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 35 (slopeOrbit 35 17 j) = 4) ⊆ {5} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 5
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(37, 18)`: `35 -> 33 -> 29 -> 21 -> 5 -> 3 -> 11 -> 7 -> 19 -> 1 -> 27 -> 17 -> 31 -> 25 -> 13 -> 15 -> 23 -> 9`, canonical gaps
`1, 1, 1, 1, 3, 4, 2, 3, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3` - period `18`, band-4 count `1` (positions `{6}`). -/
private theorem towerME_cyc_37_18 :
    slopeOrbit 37 18 (1 + 18) = slopeOrbit 37 18 1
      ∧ towerBand4CycleCount 37 18 18 ≤ 1 := by
  have e0 : slopeOrbit 37 18 0 = 18 := rfl
  have e1 : slopeOrbit 37 18 1 = 35 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 37 18 2 = 33 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 37 18 3 = 29 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 37 18 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 37 18 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 37 18 6 = 3 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 37 18 7 = 11 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 37 18 8 = 7 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 37 18 9 = 19 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 37 18 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 37 18 11 = 27 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 37 18 12 = 17 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 37 18 13 = 31 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 37 18 14 = 25 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 37 18 15 = 13 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 37 18 16 = 15 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 37 18 17 = 23 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 37 18 18 = 9 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 37 18 19 = 35 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 37 18 19 = slopeOrbit 37 18 1
    rw [e19, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 18).filter
        (fun j => canonGap 37 (slopeOrbit 37 18 j) = 4) ⊆ {6} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 6
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(39, 1)`: `25 -> 11 -> 5 -> 1`, canonical gaps
`1, 2, 3, 6` - period `4`, band-4-FREE. -/
private theorem towerME_cyc_39_1 :
    slopeOrbit 39 1 (1 + 4) = slopeOrbit 39 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 39 (slopeOrbit 39 1 j) ≠ 4 := by
  have e0 : slopeOrbit 39 1 0 = 1 := rfl
  have e1 : slopeOrbit 39 1 1 = 25 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 1 2 = 11 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 1 3 = 5 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 1 4 = 1 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 1 5 = 25 :=
    slopeOrbit_step_eval 4 5 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 39 1 5 = slopeOrbit 39 1 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(39, 6)`: `9 -> 33 -> 27 -> 15 -> 21 -> 3`, canonical gaps
`3, 1, 1, 2, 1, 4` - period `6`, band-4 count `1` (positions `{6}`). -/
private theorem towerME_cyc_39_6 :
    slopeOrbit 39 6 (1 + 6) = slopeOrbit 39 6 1
      ∧ towerBand4CycleCount 39 6 6 ≤ 1 := by
  have e0 : slopeOrbit 39 6 0 = 6 := rfl
  have e1 : slopeOrbit 39 6 1 = 9 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 6 2 = 33 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 6 3 = 27 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 6 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 6 5 = 21 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 39 6 6 = 3 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 39 6 7 = 9 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 39 6 7 = slopeOrbit 39 6 1
    rw [e7, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 6).filter
        (fun j => canonGap 39 (slopeOrbit 39 6 j) = 4) ⊆ {6} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 6
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(39, 19)`: `37 -> 35 -> 31 -> 23 -> 7 -> 17 -> 29 -> 19`, canonical gaps
`1, 1, 1, 1, 3, 2, 1, 2` - period `8`, band-4-FREE. -/
private theorem towerME_cyc_39_19 :
    slopeOrbit 39 19 (1 + 8) = slopeOrbit 39 19 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 → canonGap 39 (slopeOrbit 39 19 j) ≠ 4 := by
  have e0 : slopeOrbit 39 19 0 = 19 := rfl
  have e1 : slopeOrbit 39 19 1 = 37 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 19 2 = 35 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 19 3 = 31 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 19 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 19 5 = 7 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 39 19 6 = 17 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 39 19 7 = 29 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 39 19 8 = 19 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 39 19 9 = 37 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 39 19 9 = slopeOrbit 39 19 1
    rw [e9, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(41, 20)`: `39 -> 37 -> 33 -> 25 -> 9 -> 31 -> 21 -> 1 -> 23 -> 5`, canonical gaps
`1, 1, 1, 1, 3, 1, 1, 6, 1, 4` - period `10`, band-4 count `1` (positions `{10}`). -/
private theorem towerME_cyc_41_20 :
    slopeOrbit 41 20 (1 + 10) = slopeOrbit 41 20 1
      ∧ towerBand4CycleCount 41 20 10 ≤ 1 := by
  have e0 : slopeOrbit 41 20 0 = 20 := rfl
  have e1 : slopeOrbit 41 20 1 = 39 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 41 20 2 = 37 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 41 20 3 = 33 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 41 20 4 = 25 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 41 20 5 = 9 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 41 20 6 = 31 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 41 20 7 = 21 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 41 20 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 41 20 9 = 23 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 41 20 10 = 5 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 41 20 11 = 39 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 41 20 11 = slopeOrbit 41 20 1
    rw [e11, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 10).filter
        (fun j => canonGap 41 (slopeOrbit 41 20 j) = 4) ⊆ {10} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 10
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(43, 21)`: `41 -> 39 -> 35 -> 27 -> 11 -> 1 -> 21`, canonical gaps
`1, 1, 1, 1, 2, 6, 2` - period `7`, band-4-FREE. -/
private theorem towerME_cyc_43_21 :
    slopeOrbit 43 21 (1 + 7) = slopeOrbit 43 21 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 43 (slopeOrbit 43 21 j) ≠ 4 := by
  have e0 : slopeOrbit 43 21 0 = 21 := rfl
  have e1 : slopeOrbit 43 21 1 = 41 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 43 21 2 = 39 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 43 21 3 = 35 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 43 21 4 = 27 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 43 21 5 = 11 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 43 21 6 = 1 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 43 21 7 = 21 :=
    slopeOrbit_step_eval 6 5 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 43 21 8 = 41 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 43 21 8 = slopeOrbit 43 21 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(45, 1)`: `19 -> 31 -> 17 -> 23 -> 1`, canonical gaps
`2, 1, 2, 1, 6` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_45_1 :
    slopeOrbit 45 1 (1 + 5) = slopeOrbit 45 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 45 (slopeOrbit 45 1 j) ≠ 4 := by
  have e0 : slopeOrbit 45 1 0 = 1 := rfl
  have e1 : slopeOrbit 45 1 1 = 19 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 1 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 1 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 1 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 1 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 1 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 1 6 = slopeOrbit 45 1 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(45, 2)`: `19 -> 31 -> 17 -> 23 -> 1`, canonical gaps
`2, 1, 2, 1, 6` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_45_2 :
    slopeOrbit 45 2 (1 + 5) = slopeOrbit 45 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 45 (slopeOrbit 45 2 j) ≠ 4 := by
  have e0 : slopeOrbit 45 2 0 = 2 := rfl
  have e1 : slopeOrbit 45 2 1 = 19 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 2 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 2 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 2 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 2 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 2 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 2 6 = slopeOrbit 45 2 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(45, 4)`: `19 -> 31 -> 17 -> 23 -> 1`, canonical gaps
`2, 1, 2, 1, 6` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_45_4 :
    slopeOrbit 45 4 (1 + 5) = slopeOrbit 45 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 45 (slopeOrbit 45 4 j) ≠ 4 := by
  have e0 : slopeOrbit 45 4 0 = 4 := rfl
  have e1 : slopeOrbit 45 4 1 = 19 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 4 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 4 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 4 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 4 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 4 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 4 6 = slopeOrbit 45 4 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(45, 7)`: `11 -> 43 -> 41 -> 37 -> 29 -> 13 -> 7`, canonical gaps
`3, 1, 1, 1, 1, 2, 3` - period `7`, band-4-FREE. -/
private theorem towerME_cyc_45_7 :
    slopeOrbit 45 7 (1 + 7) = slopeOrbit 45 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 45 (slopeOrbit 45 7 j) ≠ 4 := by
  have e0 : slopeOrbit 45 7 0 = 7 := rfl
  have e1 : slopeOrbit 45 7 1 = 11 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 7 2 = 43 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 7 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 7 4 = 37 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 7 5 = 29 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 7 6 = 13 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 45 7 7 = 7 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 45 7 8 = 11 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 7 8 = slopeOrbit 45 7 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(45, 22)`: `43 -> 41 -> 37 -> 29 -> 13 -> 7 -> 11`, canonical gaps
`1, 1, 1, 1, 2, 3, 3` - period `7`, band-4-FREE. -/
private theorem towerME_cyc_45_22 :
    slopeOrbit 45 22 (1 + 7) = slopeOrbit 45 22 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 45 (slopeOrbit 45 22 j) ≠ 4 := by
  have e0 : slopeOrbit 45 22 0 = 22 := rfl
  have e1 : slopeOrbit 45 22 1 = 43 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 22 2 = 41 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 22 3 = 37 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 22 4 = 29 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 22 5 = 13 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 22 6 = 7 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 45 22 7 = 11 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 45 22 8 = 43 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 22 8 = slopeOrbit 45 22 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(47, 23)`: `45 -> 43 -> 39 -> 31 -> 15 -> 13 -> 5 -> 33 -> 19 -> 29 -> 11 -> 41 -> 35 -> 23`, canonical gaps
`1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 2` - period `14`, band-4 count `1` (positions `{7}`). -/
private theorem towerME_cyc_47_23 :
    slopeOrbit 47 23 (1 + 14) = slopeOrbit 47 23 1
      ∧ towerBand4CycleCount 47 23 14 ≤ 1 := by
  have e0 : slopeOrbit 47 23 0 = 23 := rfl
  have e1 : slopeOrbit 47 23 1 = 45 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 47 23 2 = 43 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 47 23 3 = 39 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 47 23 4 = 31 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 47 23 5 = 15 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 47 23 6 = 13 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 47 23 7 = 5 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 47 23 8 = 33 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 47 23 9 = 19 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 47 23 10 = 29 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 47 23 11 = 11 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 47 23 12 = 41 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 47 23 13 = 35 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 47 23 14 = 23 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 47 23 15 = 45 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 47 23 15 = slopeOrbit 47 23 1
    rw [e15, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 14).filter
        (fun j => canonGap 47 (slopeOrbit 47 23 j) = 4) ⊆ {7} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 7
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(49, 3)`: `47 -> 45 -> 41 -> 33 -> 17 -> 19 -> 27 -> 5 -> 31 -> 13 -> 3`, canonical gaps
`1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5` - period `11`, band-4 count `1` (positions `{8}`). -/
private theorem towerME_cyc_49_3 :
    slopeOrbit 49 3 (1 + 11) = slopeOrbit 49 3 1
      ∧ towerBand4CycleCount 49 3 11 ≤ 1 := by
  have e0 : slopeOrbit 49 3 0 = 3 := rfl
  have e1 : slopeOrbit 49 3 1 = 47 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 49 3 2 = 45 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 49 3 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 49 3 4 = 33 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 49 3 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 49 3 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 49 3 7 = 27 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 49 3 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 49 3 9 = 31 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 49 3 10 = 13 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 49 3 11 = 3 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 49 3 12 = 47 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 49 3 12 = slopeOrbit 49 3 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 49 (slopeOrbit 49 3 j) = 4) ⊆ {8} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 8
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(49, 24)`: `47 -> 45 -> 41 -> 33 -> 17 -> 19 -> 27 -> 5 -> 31 -> 13 -> 3`, canonical gaps
`1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5` - period `11`, band-4 count `1` (positions `{8}`). -/
private theorem towerME_cyc_49_24 :
    slopeOrbit 49 24 (1 + 11) = slopeOrbit 49 24 1
      ∧ towerBand4CycleCount 49 24 11 ≤ 1 := by
  have e0 : slopeOrbit 49 24 0 = 24 := rfl
  have e1 : slopeOrbit 49 24 1 = 47 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 49 24 2 = 45 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 49 24 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 49 24 4 = 33 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 49 24 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 49 24 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 49 24 7 = 27 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 49 24 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 49 24 9 = 31 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 49 24 10 = 13 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 49 24 11 = 3 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 49 24 12 = 47 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 49 24 12 = slopeOrbit 49 24 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 49 (slopeOrbit 49 24 j) = 4) ⊆ {8} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 8
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(51, 1)`: `13 -> 1`, canonical gaps
`2, 6` - period `2`, band-4-FREE. -/
private theorem towerME_cyc_51_1 :
    slopeOrbit 51 1 (1 + 2) = slopeOrbit 51 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 1 j) ≠ 4 := by
  have e0 : slopeOrbit 51 1 0 = 1 := rfl
  have e1 : slopeOrbit 51 1 1 = 13 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 1 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 1 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 1 3 = slopeOrbit 51 1 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(51, 8)`: `13 -> 1`, canonical gaps
`2, 6` - period `2`, band-4-FREE. -/
private theorem towerME_cyc_51_8 :
    slopeOrbit 51 8 (1 + 2) = slopeOrbit 51 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 8 j) ≠ 4 := by
  have e0 : slopeOrbit 51 8 0 = 8 := rfl
  have e1 : slopeOrbit 51 8 1 = 13 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 8 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 8 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 8 3 = slopeOrbit 51 8 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(51, 25)`: `49 -> 47 -> 43 -> 35 -> 19 -> 25`, canonical gaps
`1, 1, 1, 1, 2, 2` - period `6`, band-4-FREE. -/
private theorem towerME_cyc_51_25 :
    slopeOrbit 51 25 (1 + 6) = slopeOrbit 51 25 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 51 (slopeOrbit 51 25 j) ≠ 4 := by
  have e0 : slopeOrbit 51 25 0 = 25 := rfl
  have e1 : slopeOrbit 51 25 1 = 49 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 25 2 = 47 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 25 3 = 43 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 51 25 4 = 35 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 51 25 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 51 25 6 = 25 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 51 25 7 = 49 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 25 7 = slopeOrbit 51 25 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(53, 26)`: `51 -> 49 -> 45 -> 37 -> 21 -> 31 -> 9 -> 19 -> 23 -> 39 -> 25 -> 47 -> 41 -> 29 -> 5 -> 27 -> 1 -> 11 -> 35 -> 17 -> 15 -> 7 -> 3 -> 43 -> 33 -> 13`, canonical gaps
`1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 1, 6, 3, 1, 2, 2, 3, 5, 1, 1, 3` - period `26`, band-4 count `1` (positions `{15}`). -/
private theorem towerME_cyc_53_26 :
    slopeOrbit 53 26 (1 + 26) = slopeOrbit 53 26 1
      ∧ towerBand4CycleCount 53 26 26 ≤ 1 := by
  have e0 : slopeOrbit 53 26 0 = 26 := rfl
  have e1 : slopeOrbit 53 26 1 = 51 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 53 26 2 = 49 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 53 26 3 = 45 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 53 26 4 = 37 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 53 26 5 = 21 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 53 26 6 = 31 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 53 26 7 = 9 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 53 26 8 = 19 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 53 26 9 = 23 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 53 26 10 = 39 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 53 26 11 = 25 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 53 26 12 = 47 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 53 26 13 = 41 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 53 26 14 = 29 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 53 26 15 = 5 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 53 26 16 = 27 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 53 26 17 = 1 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 53 26 18 = 11 :=
    slopeOrbit_step_eval 17 5 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 53 26 19 = 35 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 53 26 20 = 17 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 53 26 21 = 15 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 53 26 22 = 7 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 53 26 23 = 3 :=
    slopeOrbit_step_eval 22 2 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 53 26 24 = 43 :=
    slopeOrbit_step_eval 23 4 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 53 26 25 = 33 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 53 26 26 = 13 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 53 26 27 = 51 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 53 26 27 = slopeOrbit 53 26 1
    rw [e27, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 26).filter
        (fun j => canonGap 53 (slopeOrbit 53 26 j) = 4) ⊆ {15} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 15
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(55, 2)`: `9 -> 17 -> 13 -> 49 -> 43 -> 31 -> 7 -> 1`, canonical gaps
`3, 2, 3, 1, 1, 1, 3, 6` - period `8`, band-4-FREE. -/
private theorem towerME_cyc_55_2 :
    slopeOrbit 55 2 (1 + 8) = slopeOrbit 55 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 → canonGap 55 (slopeOrbit 55 2 j) ≠ 4 := by
  have e0 : slopeOrbit 55 2 0 = 2 := rfl
  have e1 : slopeOrbit 55 2 1 = 9 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 55 2 2 = 17 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 55 2 3 = 13 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 55 2 4 = 49 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 55 2 5 = 43 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 55 2 6 = 31 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 55 2 7 = 7 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 55 2 8 = 1 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 55 2 9 = 9 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 55 2 9 = slopeOrbit 55 2 1
    rw [e9, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(55, 5)`: `25 -> 45 -> 35 -> 15 -> 5`, canonical gaps
`2, 1, 1, 2, 4` - period `5`, band-4 count `1` (positions `{5}`). -/
private theorem towerME_cyc_55_5 :
    slopeOrbit 55 5 (1 + 5) = slopeOrbit 55 5 1
      ∧ towerBand4CycleCount 55 5 5 ≤ 1 := by
  have e0 : slopeOrbit 55 5 0 = 5 := rfl
  have e1 : slopeOrbit 55 5 1 = 25 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 55 5 2 = 45 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 55 5 3 = 35 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 55 5 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 55 5 5 = 5 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 55 5 6 = 25 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 55 5 6 = slopeOrbit 55 5 1
    rw [e6, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 55 (slopeOrbit 55 5 j) = 4) ⊆ {5} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 5
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(55, 27)`: `53 -> 51 -> 47 -> 39 -> 23 -> 37 -> 19 -> 21 -> 29 -> 3 -> 41 -> 27`, canonical gaps
`1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2` - period `12`, band-4-FREE. -/
private theorem towerME_cyc_55_27 :
    slopeOrbit 55 27 (1 + 12) = slopeOrbit 55 27 1
      ∧ ∀ j, 1 ≤ j → j ≤ 12 → canonGap 55 (slopeOrbit 55 27 j) ≠ 4 := by
  have e0 : slopeOrbit 55 27 0 = 27 := rfl
  have e1 : slopeOrbit 55 27 1 = 53 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 55 27 2 = 51 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 55 27 3 = 47 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 55 27 4 = 39 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 55 27 5 = 23 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 55 27 6 = 37 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 55 27 7 = 19 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 55 27 8 = 21 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 55 27 9 = 29 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 55 27 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 55 27 11 = 41 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 55 27 12 = 27 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 55 27 13 = 53 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 55 27 13 = slopeOrbit 55 27 1
    rw [e13, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)
    · rw [e10]; exact canonGap_ne_four_of_band (by omega)
    · rw [e11]; exact canonGap_ne_four_of_band (by omega)
    · rw [e12]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(57, 1)`: `7 -> 55 -> 53 -> 49 -> 41 -> 25 -> 43 -> 29 -> 1`, canonical gaps
`4, 1, 1, 1, 1, 2, 1, 1, 6` - period `9`, band-4 count `1` (positions `{1}`). -/
private theorem towerME_cyc_57_1 :
    slopeOrbit 57 1 (1 + 9) = slopeOrbit 57 1 1
      ∧ towerBand4CycleCount 57 1 9 ≤ 1 := by
  have e0 : slopeOrbit 57 1 0 = 1 := rfl
  have e1 : slopeOrbit 57 1 1 = 7 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 1 2 = 55 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 1 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 1 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 1 5 = 41 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 1 6 = 25 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 1 7 = 43 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 1 8 = 29 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 1 9 = 1 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 1 10 = 7 :=
    slopeOrbit_step_eval 9 5 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 57 1 10 = slopeOrbit 57 1 1
    rw [e10, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 57 (slopeOrbit 57 1 j) = 4) ⊆ {1} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exact Finset.mem_singleton_self 1
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(57, 9)`: `15 -> 3 -> 39 -> 21 -> 27 -> 51 -> 45 -> 33 -> 9`, canonical gaps
`2, 5, 1, 2, 2, 1, 1, 1, 3` - period `9`, band-4-FREE. -/
private theorem towerME_cyc_57_9 :
    slopeOrbit 57 9 (1 + 9) = slopeOrbit 57 9 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 57 (slopeOrbit 57 9 j) ≠ 4 := by
  have e0 : slopeOrbit 57 9 0 = 9 := rfl
  have e1 : slopeOrbit 57 9 1 = 15 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 9 2 = 3 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 9 3 = 39 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 9 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 9 5 = 27 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 9 6 = 51 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 9 7 = 45 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 9 8 = 33 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 9 9 = 9 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 9 10 = 15 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 57 9 10 = slopeOrbit 57 9 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(57, 28)`: `55 -> 53 -> 49 -> 41 -> 25 -> 43 -> 29 -> 1 -> 7`, canonical gaps
`1, 1, 1, 1, 2, 1, 1, 6, 4` - period `9`, band-4 count `1` (positions `{9}`). -/
private theorem towerME_cyc_57_28 :
    slopeOrbit 57 28 (1 + 9) = slopeOrbit 57 28 1
      ∧ towerBand4CycleCount 57 28 9 ≤ 1 := by
  have e0 : slopeOrbit 57 28 0 = 28 := rfl
  have e1 : slopeOrbit 57 28 1 = 55 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 28 2 = 53 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 28 3 = 49 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 28 4 = 41 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 28 5 = 25 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 28 6 = 43 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 28 7 = 29 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 28 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 28 9 = 7 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 28 10 = 55 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 57 28 10 = slopeOrbit 57 28 1
    rw [e10, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 57 (slopeOrbit 57 28 j) = 4) ⊆ {9} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 9
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(59, 29)`: `57 -> 55 -> 51 -> 43 -> 27 -> 49 -> 39 -> 19 -> 17 -> 9 -> 13 -> 45 -> 31 -> 3 -> 37 -> 15 -> 1 -> 5 -> 21 -> 25 -> 41 -> 23 -> 33 -> 7 -> 53 -> 47 -> 35 -> 11 -> 29`, canonical gaps
`1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 2, 6, 4, 2, 2, 1, 2, 1, 4, 1, 1, 1, 3, 2` - period `29`, band-4 count `2` (positions `{18, 24}`). -/
private theorem towerME_cyc_59_29 :
    slopeOrbit 59 29 (1 + 29) = slopeOrbit 59 29 1
      ∧ towerBand4CycleCount 59 29 29 ≤ 2 := by
  have e0 : slopeOrbit 59 29 0 = 29 := rfl
  have e1 : slopeOrbit 59 29 1 = 57 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 59 29 2 = 55 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 59 29 3 = 51 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 59 29 4 = 43 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 59 29 5 = 27 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 59 29 6 = 49 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 59 29 7 = 39 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 59 29 8 = 19 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 59 29 9 = 17 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 59 29 10 = 9 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 59 29 11 = 13 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 59 29 12 = 45 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 59 29 13 = 31 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 59 29 14 = 3 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 59 29 15 = 37 :=
    slopeOrbit_step_eval 14 4 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 59 29 16 = 15 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 59 29 17 = 1 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 59 29 18 = 5 :=
    slopeOrbit_step_eval 17 5 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 59 29 19 = 21 :=
    slopeOrbit_step_eval 18 3 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 59 29 20 = 25 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 59 29 21 = 41 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 59 29 22 = 23 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 59 29 23 = 33 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 59 29 24 = 7 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 59 29 25 = 53 :=
    slopeOrbit_step_eval 24 3 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 59 29 26 = 47 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 59 29 27 = 35 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 59 29 28 = 11 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 59 29 29 = 29 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 59 29 30 = 57 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 59 29 30 = slopeOrbit 59 29 1
    rw [e30, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 29).filter
        (fun j => canonGap 59 (slopeOrbit 59 29 j) = 4) ⊆ {18, 24} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 18 {24}
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 24)
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e28] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e29] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 18 ({24} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(61, 30)`: `59 -> 57 -> 53 -> 45 -> 29 -> 55 -> 49 -> 37 -> 13 -> 43 -> 25 -> 39 -> 17 -> 7 -> 51 -> 41 -> 21 -> 23 -> 31 -> 1 -> 3 -> 35 -> 9 -> 11 -> 27 -> 47 -> 33 -> 5 -> 19 -> 15`, canonical gaps
`1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6, 5, 1, 3, 3, 2, 1, 1, 4, 2, 3` - period `30`, band-4 count `2` (positions `{14, 28}`). -/
private theorem towerME_cyc_61_30 :
    slopeOrbit 61 30 (1 + 30) = slopeOrbit 61 30 1
      ∧ towerBand4CycleCount 61 30 30 ≤ 2 := by
  have e0 : slopeOrbit 61 30 0 = 30 := rfl
  have e1 : slopeOrbit 61 30 1 = 59 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 61 30 2 = 57 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 61 30 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 61 30 4 = 45 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 61 30 5 = 29 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 61 30 6 = 55 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 61 30 7 = 49 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 61 30 8 = 37 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 61 30 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 61 30 10 = 43 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 61 30 11 = 25 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 61 30 12 = 39 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 61 30 13 = 17 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 61 30 14 = 7 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 61 30 15 = 51 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 61 30 16 = 41 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 61 30 17 = 21 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 61 30 18 = 23 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 61 30 19 = 31 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 61 30 20 = 1 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 61 30 21 = 3 :=
    slopeOrbit_step_eval 20 5 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 61 30 22 = 35 :=
    slopeOrbit_step_eval 21 4 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 61 30 23 = 9 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 61 30 24 = 11 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 61 30 25 = 27 :=
    slopeOrbit_step_eval 24 2 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 61 30 26 = 47 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 61 30 27 = 33 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 61 30 28 = 5 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 61 30 29 = 19 :=
    slopeOrbit_step_eval 28 3 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 61 30 30 = 15 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 61 30 31 = 59 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 61 30 31 = slopeOrbit 61 30 1
    rw [e31, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 30).filter
        (fun j => canonGap 61 (slopeOrbit 61 30 j) = 4) ⊆ {14, 28} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 14 {28}
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 28)
      · rw [e29] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e30] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 14 ({28} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(63, 1)`: `1`, canonical gaps
`6` - period `1`, band-4-FREE. -/
private theorem towerME_cyc_63_1 :
    slopeOrbit 63 1 (1 + 1) = slopeOrbit 63 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → canonGap 63 (slopeOrbit 63 1 j) ≠ 4 := by
  have e0 : slopeOrbit 63 1 0 = 1 := rfl
  have e1 : slopeOrbit 63 1 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 1 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 1 2 = slopeOrbit 63 1 1
    rw [e2, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(63, 3)`: `33 -> 3`, canonical gaps
`1, 5` - period `2`, band-4-FREE. -/
private theorem towerME_cyc_63_3 :
    slopeOrbit 63 3 (1 + 2) = slopeOrbit 63 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 63 (slopeOrbit 63 3 j) ≠ 4 := by
  have e0 : slopeOrbit 63 3 0 = 3 := rfl
  have e1 : slopeOrbit 63 3 1 = 33 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 3 2 = 3 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 3 3 = 33 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 3 3 = slopeOrbit 63 3 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(63, 4)`: `1`, canonical gaps
`6` - period `1`, band-4-FREE. -/
private theorem towerME_cyc_63_4 :
    slopeOrbit 63 4 (1 + 1) = slopeOrbit 63 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → canonGap 63 (slopeOrbit 63 4 j) ≠ 4 := by
  have e0 : slopeOrbit 63 4 0 = 4 := rfl
  have e1 : slopeOrbit 63 4 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 4 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 4 2 = slopeOrbit 63 4 1
    rw [e2, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(63, 10)`: `17 -> 5`, canonical gaps
`2, 4` - period `2`, band-4 count `1` (positions `{2}`). -/
private theorem towerME_cyc_63_10 :
    slopeOrbit 63 10 (1 + 2) = slopeOrbit 63 10 1
      ∧ towerBand4CycleCount 63 10 2 ≤ 1 := by
  have e0 : slopeOrbit 63 10 0 = 10 := rfl
  have e1 : slopeOrbit 63 10 1 = 17 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 10 2 = 5 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 10 3 = 17 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 63 10 3 = slopeOrbit 63 10 1
    rw [e3, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 2).filter
        (fun j => canonGap 63 (slopeOrbit 63 10 j) = 4) ⊆ {2} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(63, 31)`: `61 -> 59 -> 55 -> 47 -> 31`, canonical gaps
`1, 1, 1, 1, 2` - period `5`, band-4-FREE. -/
private theorem towerME_cyc_63_31 :
    slopeOrbit 63 31 (1 + 5) = slopeOrbit 63 31 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 63 (slopeOrbit 63 31 j) ≠ 4 := by
  have e0 : slopeOrbit 63 31 0 = 31 := rfl
  have e1 : slopeOrbit 63 31 1 = 61 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 31 2 = 59 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 31 3 = 55 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 63 31 4 = 47 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 63 31 5 = 31 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 63 31 6 = 61 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 31 6 = slopeOrbit 63 31 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(65, 2)`: `63 -> 61 -> 57 -> 49 -> 33 -> 1`, canonical gaps
`1, 1, 1, 1, 1, 7` - period `6`, band-4-FREE. -/
private theorem towerME_cyc_65_2 :
    slopeOrbit 65 2 (1 + 6) = slopeOrbit 65 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 2 j) ≠ 4 := by
  have e0 : slopeOrbit 65 2 0 = 2 := rfl
  have e1 : slopeOrbit 65 2 1 = 63 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 65 2 2 = 61 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 65 2 3 = 57 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 65 2 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 65 2 5 = 33 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 65 2 6 = 1 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 65 2 7 = 63 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 65 2 7 = slopeOrbit 65 2 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(65, 6)`: `31 -> 59 -> 53 -> 41 -> 17 -> 3`, canonical gaps
`2, 1, 1, 1, 2, 5` - period `6`, band-4-FREE. -/
private theorem towerME_cyc_65_6 :
    slopeOrbit 65 6 (1 + 6) = slopeOrbit 65 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 6 j) ≠ 4 := by
  have e0 : slopeOrbit 65 6 0 = 6 := rfl
  have e1 : slopeOrbit 65 6 1 = 31 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 65 6 2 = 59 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 65 6 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 65 6 4 = 41 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 65 6 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 65 6 6 = 3 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 65 6 7 = 31 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 65 6 7 = slopeOrbit 65 6 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(65, 32)`: `63 -> 61 -> 57 -> 49 -> 33 -> 1`, canonical gaps
`1, 1, 1, 1, 1, 7` - period `6`, band-4-FREE. -/
private theorem towerME_cyc_65_32 :
    slopeOrbit 65 32 (1 + 6) = slopeOrbit 65 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 32 j) ≠ 4 := by
  have e0 : slopeOrbit 65 32 0 = 32 := rfl
  have e1 : slopeOrbit 65 32 1 = 63 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 65 32 2 = 61 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 65 32 3 = 57 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 65 32 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 65 32 5 = 33 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 65 32 6 = 1 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 65 32 7 = 63 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 65 32 7 = slopeOrbit 65 32 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(67, 33)`: `65 -> 63 -> 59 -> 51 -> 35 -> 3 -> 29 -> 49 -> 31 -> 57 -> 47 -> 27 -> 41 -> 15 -> 53 -> 39 -> 11 -> 21 -> 17 -> 1 -> 61 -> 55 -> 43 -> 19 -> 9 -> 5 -> 13 -> 37 -> 7 -> 45 -> 23 -> 25 -> 33`, canonical gaps
`1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 7, 1, 1, 1, 2, 3, 4, 3, 1, 4, 1, 2, 2, 2` - period `33`, band-4 count `2` (positions `{26, 29}`). -/
private theorem towerME_cyc_67_33 :
    slopeOrbit 67 33 (1 + 33) = slopeOrbit 67 33 1
      ∧ towerBand4CycleCount 67 33 33 ≤ 2 := by
  have e0 : slopeOrbit 67 33 0 = 33 := rfl
  have e1 : slopeOrbit 67 33 1 = 65 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 67 33 2 = 63 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 67 33 3 = 59 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 67 33 4 = 51 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 67 33 5 = 35 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 67 33 6 = 3 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 67 33 7 = 29 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 67 33 8 = 49 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 67 33 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 67 33 10 = 57 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 67 33 11 = 47 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 67 33 12 = 27 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 67 33 13 = 41 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 67 33 14 = 15 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 67 33 15 = 53 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 67 33 16 = 39 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 67 33 17 = 11 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 67 33 18 = 21 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 67 33 19 = 17 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 67 33 20 = 1 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 67 33 21 = 61 :=
    slopeOrbit_step_eval 20 6 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 67 33 22 = 55 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 67 33 23 = 43 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 67 33 24 = 19 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 67 33 25 = 9 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 67 33 26 = 5 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 67 33 27 = 13 :=
    slopeOrbit_step_eval 26 3 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 67 33 28 = 37 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 67 33 29 = 7 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 67 33 30 = 45 :=
    slopeOrbit_step_eval 29 3 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 67 33 31 = 23 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 67 33 32 = 25 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 67 33 33 = 33 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 67 33 34 = 65 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 67 33 34 = slopeOrbit 67 33 1
    rw [e34, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 33).filter
        (fun j => canonGap 67 (slopeOrbit 67 33 j) = 4) ⊆ {26, 29} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 26 {29}
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e28] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 29)
      · rw [e30] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e31] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e32] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e33] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 26 ({29} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(69, 1)`: `59 -> 49 -> 29 -> 47 -> 25 -> 31 -> 55 -> 41 -> 13 -> 35 -> 1`, canonical gaps
`1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7` - period `11`, band-4-FREE. -/
private theorem towerME_cyc_69_1 :
    slopeOrbit 69 1 (1 + 11) = slopeOrbit 69 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 11 → canonGap 69 (slopeOrbit 69 1 j) ≠ 4 := by
  have e0 : slopeOrbit 69 1 0 = 1 := rfl
  have e1 : slopeOrbit 69 1 1 = 59 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 69 1 2 = 49 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 69 1 3 = 29 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 69 1 4 = 47 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 69 1 5 = 25 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 69 1 6 = 31 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 69 1 7 = 55 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 69 1 8 = 41 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 69 1 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 69 1 10 = 35 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 69 1 11 = 1 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 69 1 12 = 59 :=
    slopeOrbit_step_eval 11 6 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 69 1 12 = slopeOrbit 69 1 1
    rw [e12, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)
    · rw [e10]; exact canonGap_ne_four_of_band (by omega)
    · rw [e11]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(69, 11)`: `19 -> 7 -> 43 -> 17 -> 67 -> 65 -> 61 -> 53 -> 37 -> 5 -> 11`, canonical gaps
`2, 4, 1, 3, 1, 1, 1, 1, 1, 4, 3` - period `11`, band-4 count `2` (positions `{2, 10}`). -/
private theorem towerME_cyc_69_11 :
    slopeOrbit 69 11 (1 + 11) = slopeOrbit 69 11 1
      ∧ towerBand4CycleCount 69 11 11 ≤ 2 := by
  have e0 : slopeOrbit 69 11 0 = 11 := rfl
  have e1 : slopeOrbit 69 11 1 = 19 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 69 11 2 = 7 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 69 11 3 = 43 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 69 11 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 69 11 5 = 67 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 69 11 6 = 65 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 69 11 7 = 61 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 69 11 8 = 53 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 69 11 9 = 37 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 69 11 10 = 5 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 69 11 11 = 11 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 69 11 12 = 19 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 69 11 12 = slopeOrbit 69 11 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 69 (slopeOrbit 69 11 j) = 4) ⊆ {2, 10} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 2 {10}
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 10)
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 2 ({10} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(69, 34)`: `67 -> 65 -> 61 -> 53 -> 37 -> 5 -> 11 -> 19 -> 7 -> 43 -> 17`, canonical gaps
`1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3` - period `11`, band-4 count `2` (positions `{6, 9}`). -/
private theorem towerME_cyc_69_34 :
    slopeOrbit 69 34 (1 + 11) = slopeOrbit 69 34 1
      ∧ towerBand4CycleCount 69 34 11 ≤ 2 := by
  have e0 : slopeOrbit 69 34 0 = 34 := rfl
  have e1 : slopeOrbit 69 34 1 = 67 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 69 34 2 = 65 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 69 34 3 = 61 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 69 34 4 = 53 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 69 34 5 = 37 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 69 34 6 = 5 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 69 34 7 = 11 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 69 34 8 = 19 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 69 34 9 = 7 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 69 34 10 = 43 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 69 34 11 = 17 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 69 34 12 = 67 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 69 34 12 = slopeOrbit 69 34 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 69 (slopeOrbit 69 34 j) = 4) ⊆ {6, 9} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 6 {9}
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 9)
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 6 ({9} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(71, 35)`: `69 -> 67 -> 63 -> 55 -> 39 -> 7 -> 41 -> 11 -> 17 -> 65 -> 59 -> 47 -> 23 -> 21 -> 13 -> 33 -> 61 -> 51 -> 31 -> 53 -> 35`, canonical gaps
`1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2` - period `21`, band-4 count `1` (positions `{6}`). -/
private theorem towerME_cyc_71_35 :
    slopeOrbit 71 35 (1 + 21) = slopeOrbit 71 35 1
      ∧ towerBand4CycleCount 71 35 21 ≤ 1 := by
  have e0 : slopeOrbit 71 35 0 = 35 := rfl
  have e1 : slopeOrbit 71 35 1 = 69 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 71 35 2 = 67 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 71 35 3 = 63 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 71 35 4 = 55 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 71 35 5 = 39 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 71 35 6 = 7 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 71 35 7 = 41 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 71 35 8 = 11 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 71 35 9 = 17 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 71 35 10 = 65 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 71 35 11 = 59 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 71 35 12 = 47 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 71 35 13 = 23 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 71 35 14 = 21 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 71 35 15 = 13 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 71 35 16 = 33 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 71 35 17 = 61 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 71 35 18 = 51 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 71 35 19 = 31 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 71 35 20 = 53 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 71 35 21 = 35 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 71 35 22 = 69 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 71 35 22 = slopeOrbit 71 35 1
    rw [e22, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 21).filter
        (fun j => canonGap 71 (slopeOrbit 71 35 j) = 4) ⊆ {6} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 6
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(73, 36)`: `71 -> 69 -> 65 -> 57 -> 41 -> 9`, canonical gaps
`1, 1, 1, 1, 1, 4` - period `6`, band-4 count `1` (positions `{6}`). -/
private theorem towerME_cyc_73_36 :
    slopeOrbit 73 36 (1 + 6) = slopeOrbit 73 36 1
      ∧ towerBand4CycleCount 73 36 6 ≤ 1 := by
  have e0 : slopeOrbit 73 36 0 = 36 := rfl
  have e1 : slopeOrbit 73 36 1 = 71 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 73 36 2 = 69 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 73 36 3 = 65 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 73 36 4 = 57 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 73 36 5 = 41 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 73 36 6 = 9 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 73 36 7 = 71 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 73 36 7 = slopeOrbit 73 36 1
    rw [e7, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 6).filter
        (fun j => canonGap 73 (slopeOrbit 73 36 j) = 4) ⊆ {6} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 6
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(75, 1)`: `53 -> 31 -> 49 -> 23 -> 17 -> 61 -> 47 -> 19 -> 1`, canonical gaps
`1, 2, 1, 2, 3, 1, 1, 2, 7` - period `9`, band-4-FREE. -/
private theorem towerME_cyc_75_1 :
    slopeOrbit 75 1 (1 + 9) = slopeOrbit 75 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 75 (slopeOrbit 75 1 j) ≠ 4 := by
  have e0 : slopeOrbit 75 1 0 = 1 := rfl
  have e1 : slopeOrbit 75 1 1 = 53 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 1 2 = 31 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 1 3 = 49 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 1 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 1 5 = 17 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 1 6 = 61 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 1 7 = 47 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 1 8 = 19 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 1 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 1 10 = 53 :=
    slopeOrbit_step_eval 9 6 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 75 1 10 = slopeOrbit 75 1 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(75, 2)`: `53 -> 31 -> 49 -> 23 -> 17 -> 61 -> 47 -> 19 -> 1`, canonical gaps
`1, 2, 1, 2, 3, 1, 1, 2, 7` - period `9`, band-4-FREE. -/
private theorem towerME_cyc_75_2 :
    slopeOrbit 75 2 (1 + 9) = slopeOrbit 75 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 75 (slopeOrbit 75 2 j) ≠ 4 := by
  have e0 : slopeOrbit 75 2 0 = 2 := rfl
  have e1 : slopeOrbit 75 2 1 = 53 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 2 2 = 31 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 2 3 = 49 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 2 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 2 5 = 17 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 2 6 = 61 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 2 7 = 47 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 2 8 = 19 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 2 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 2 10 = 53 :=
    slopeOrbit_step_eval 9 6 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 75 2 10 = slopeOrbit 75 2 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(75, 7)`: `37 -> 73 -> 71 -> 67 -> 59 -> 43 -> 11 -> 13 -> 29 -> 41 -> 7`, canonical gaps
`2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4` - period `11`, band-4 count `1` (positions `{11}`). -/
private theorem towerME_cyc_75_7 :
    slopeOrbit 75 7 (1 + 11) = slopeOrbit 75 7 1
      ∧ towerBand4CycleCount 75 7 11 ≤ 1 := by
  have e0 : slopeOrbit 75 7 0 = 7 := rfl
  have e1 : slopeOrbit 75 7 1 = 37 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 7 2 = 73 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 7 3 = 71 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 7 4 = 67 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 7 5 = 59 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 7 6 = 43 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 7 7 = 11 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 7 8 = 13 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 7 9 = 29 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 7 10 = 41 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 75 7 11 = 7 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 75 7 12 = 37 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 75 7 12 = slopeOrbit 75 7 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 75 (slopeOrbit 75 7 j) = 4) ⊆ {11} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 11
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(75, 12)`: `21 -> 9 -> 69 -> 63 -> 51 -> 27 -> 33 -> 57 -> 39 -> 3`, canonical gaps
`2, 4, 1, 1, 1, 2, 2, 1, 1, 5` - period `10`, band-4 count `1` (positions `{2}`). -/
private theorem towerME_cyc_75_12 :
    slopeOrbit 75 12 (1 + 10) = slopeOrbit 75 12 1
      ∧ towerBand4CycleCount 75 12 10 ≤ 1 := by
  have e0 : slopeOrbit 75 12 0 = 12 := rfl
  have e1 : slopeOrbit 75 12 1 = 21 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 12 2 = 9 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 12 3 = 69 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 12 4 = 63 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 12 5 = 51 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 12 6 = 27 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 12 7 = 33 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 12 8 = 57 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 12 9 = 39 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 12 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 75 12 11 = 21 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 75 12 11 = slopeOrbit 75 12 1
    rw [e11, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 10).filter
        (fun j => canonGap 75 (slopeOrbit 75 12 j) = 4) ⊆ {2} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 2
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(75, 37)`: `73 -> 71 -> 67 -> 59 -> 43 -> 11 -> 13 -> 29 -> 41 -> 7 -> 37`, canonical gaps
`1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2` - period `11`, band-4 count `1` (positions `{10}`). -/
private theorem towerME_cyc_75_37 :
    slopeOrbit 75 37 (1 + 11) = slopeOrbit 75 37 1
      ∧ towerBand4CycleCount 75 37 11 ≤ 1 := by
  have e0 : slopeOrbit 75 37 0 = 37 := rfl
  have e1 : slopeOrbit 75 37 1 = 73 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 37 2 = 71 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 37 3 = 67 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 37 4 = 59 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 37 5 = 43 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 37 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 37 7 = 13 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 37 8 = 29 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 37 9 = 41 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 37 10 = 7 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 75 37 11 = 37 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 75 37 12 = 73 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 75 37 12 = slopeOrbit 75 37 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 75 (slopeOrbit 75 37 j) = 4) ⊆ {10} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 10
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(77, 3)`: `19 -> 75 -> 73 -> 69 -> 61 -> 45 -> 13 -> 27 -> 31 -> 47 -> 17 -> 59 -> 41 -> 5 -> 3`, canonical gaps
`3, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 5` - period `15`, band-4 count `1` (positions `{14}`). -/
private theorem towerME_cyc_77_3 :
    slopeOrbit 77 3 (1 + 15) = slopeOrbit 77 3 1
      ∧ towerBand4CycleCount 77 3 15 ≤ 1 := by
  have e0 : slopeOrbit 77 3 0 = 3 := rfl
  have e1 : slopeOrbit 77 3 1 = 19 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 77 3 2 = 75 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 77 3 3 = 73 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 77 3 4 = 69 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 77 3 5 = 61 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 77 3 6 = 45 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 77 3 7 = 13 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 77 3 8 = 27 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 77 3 9 = 31 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 77 3 10 = 47 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 77 3 11 = 17 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 77 3 12 = 59 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 77 3 13 = 41 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 77 3 14 = 5 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 77 3 15 = 3 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 77 3 16 = 19 :=
    slopeOrbit_step_eval 15 4 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 77 3 16 = slopeOrbit 77 3 1
    rw [e16, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 15).filter
        (fun j => canonGap 77 (slopeOrbit 77 3 j) = 4) ⊆ {14} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 14
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(77, 5)`: `3 -> 19 -> 75 -> 73 -> 69 -> 61 -> 45 -> 13 -> 27 -> 31 -> 47 -> 17 -> 59 -> 41 -> 5`, canonical gaps
`5, 3, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4` - period `15`, band-4 count `1` (positions `{15}`). -/
private theorem towerME_cyc_77_5 :
    slopeOrbit 77 5 (1 + 15) = slopeOrbit 77 5 1
      ∧ towerBand4CycleCount 77 5 15 ≤ 1 := by
  have e0 : slopeOrbit 77 5 0 = 5 := rfl
  have e1 : slopeOrbit 77 5 1 = 3 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 77 5 2 = 19 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 77 5 3 = 75 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 77 5 4 = 73 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 77 5 5 = 69 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 77 5 6 = 61 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 77 5 7 = 45 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 77 5 8 = 13 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 77 5 9 = 27 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 77 5 10 = 31 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 77 5 11 = 47 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 77 5 12 = 17 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 77 5 13 = 59 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 77 5 14 = 41 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 77 5 15 = 5 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 77 5 16 = 3 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 77 5 16 = slopeOrbit 77 5 1
    rw [e16, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 15).filter
        (fun j => canonGap 77 (slopeOrbit 77 5 j) = 4) ⊆ {15} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 15
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(77, 38)`: `75 -> 73 -> 69 -> 61 -> 45 -> 13 -> 27 -> 31 -> 47 -> 17 -> 59 -> 41 -> 5 -> 3 -> 19`, canonical gaps
`1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 5, 3` - period `15`, band-4 count `1` (positions `{13}`). -/
private theorem towerME_cyc_77_38 :
    slopeOrbit 77 38 (1 + 15) = slopeOrbit 77 38 1
      ∧ towerBand4CycleCount 77 38 15 ≤ 1 := by
  have e0 : slopeOrbit 77 38 0 = 38 := rfl
  have e1 : slopeOrbit 77 38 1 = 75 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 77 38 2 = 73 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 77 38 3 = 69 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 77 38 4 = 61 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 77 38 5 = 45 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 77 38 6 = 13 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 77 38 7 = 27 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 77 38 8 = 31 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 77 38 9 = 47 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 77 38 10 = 17 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 77 38 11 = 59 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 77 38 12 = 41 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 77 38 13 = 5 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 77 38 14 = 3 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 77 38 15 = 19 :=
    slopeOrbit_step_eval 14 4 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 77 38 16 = 75 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 77 38 16 = slopeOrbit 77 38 1
    rw [e16, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 15).filter
        (fun j => canonGap 77 (slopeOrbit 77 38 j) = 4) ⊆ {13} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 13
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(79, 39)`: `77 -> 75 -> 71 -> 63 -> 47 -> 15 -> 41 -> 3 -> 17 -> 57 -> 35 -> 61 -> 43 -> 7 -> 33 -> 53 -> 27 -> 29 -> 37 -> 69 -> 59 -> 39`, canonical gaps
`1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2` - period `22`, band-4 count `1` (positions `{14}`). -/
private theorem towerME_cyc_79_39 :
    slopeOrbit 79 39 (1 + 22) = slopeOrbit 79 39 1
      ∧ towerBand4CycleCount 79 39 22 ≤ 1 := by
  have e0 : slopeOrbit 79 39 0 = 39 := rfl
  have e1 : slopeOrbit 79 39 1 = 77 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 79 39 2 = 75 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 79 39 3 = 71 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 79 39 4 = 63 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 79 39 5 = 47 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 79 39 6 = 15 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 79 39 7 = 41 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 79 39 8 = 3 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 79 39 9 = 17 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 79 39 10 = 57 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 79 39 11 = 35 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 79 39 12 = 61 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 79 39 13 = 43 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 79 39 14 = 7 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 79 39 15 = 33 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 79 39 16 = 53 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 79 39 17 = 27 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 79 39 18 = 29 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 79 39 19 = 37 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 79 39 20 = 69 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 79 39 21 = 59 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 79 39 22 = 39 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 79 39 23 = 77 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 79 39 23 = slopeOrbit 79 39 1
    rw [e23, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 22).filter
        (fun j => canonGap 79 (slopeOrbit 79 39 j) = 4) ⊆ {14} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 14
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(81, 1)`: `47 -> 13 -> 23 -> 11 -> 7 -> 31 -> 43 -> 5 -> 79 -> 77 -> 73 -> 65 -> 49 -> 17 -> 55 -> 29 -> 35 -> 59 -> 37 -> 67 -> 53 -> 25 -> 19 -> 71 -> 61 -> 41 -> 1`, canonical gaps
`1, 3, 2, 3, 4, 2, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7` - period `27`, band-4 count `1` (positions `{5}`). -/
private theorem towerME_cyc_81_1 :
    slopeOrbit 81 1 (1 + 27) = slopeOrbit 81 1 1
      ∧ towerBand4CycleCount 81 1 27 ≤ 1 := by
  have e0 : slopeOrbit 81 1 0 = 1 := rfl
  have e1 : slopeOrbit 81 1 1 = 47 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 81 1 2 = 13 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 81 1 3 = 23 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 81 1 4 = 11 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 81 1 5 = 7 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 81 1 6 = 31 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 81 1 7 = 43 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 81 1 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 81 1 9 = 79 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 81 1 10 = 77 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 81 1 11 = 73 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 81 1 12 = 65 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 81 1 13 = 49 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 81 1 14 = 17 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 81 1 15 = 55 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 81 1 16 = 29 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 81 1 17 = 35 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 81 1 18 = 59 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 81 1 19 = 37 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 81 1 20 = 67 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 81 1 21 = 53 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 81 1 22 = 25 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 81 1 23 = 19 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 81 1 24 = 71 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 81 1 25 = 61 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 81 1 26 = 41 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 81 1 27 = 1 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 81 1 28 = 47 :=
    slopeOrbit_step_eval 27 6 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 81 1 28 = slopeOrbit 81 1 1
    rw [e28, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 27).filter
        (fun j => canonGap 81 (slopeOrbit 81 1 j) = 4) ⊆ {5} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 5
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(81, 4)`: `47 -> 13 -> 23 -> 11 -> 7 -> 31 -> 43 -> 5 -> 79 -> 77 -> 73 -> 65 -> 49 -> 17 -> 55 -> 29 -> 35 -> 59 -> 37 -> 67 -> 53 -> 25 -> 19 -> 71 -> 61 -> 41 -> 1`, canonical gaps
`1, 3, 2, 3, 4, 2, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7` - period `27`, band-4 count `1` (positions `{5}`). -/
private theorem towerME_cyc_81_4 :
    slopeOrbit 81 4 (1 + 27) = slopeOrbit 81 4 1
      ∧ towerBand4CycleCount 81 4 27 ≤ 1 := by
  have e0 : slopeOrbit 81 4 0 = 4 := rfl
  have e1 : slopeOrbit 81 4 1 = 47 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 81 4 2 = 13 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 81 4 3 = 23 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 81 4 4 = 11 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 81 4 5 = 7 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 81 4 6 = 31 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 81 4 7 = 43 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 81 4 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 81 4 9 = 79 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 81 4 10 = 77 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 81 4 11 = 73 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 81 4 12 = 65 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 81 4 13 = 49 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 81 4 14 = 17 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 81 4 15 = 55 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 81 4 16 = 29 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 81 4 17 = 35 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 81 4 18 = 59 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 81 4 19 = 37 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 81 4 20 = 67 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 81 4 21 = 53 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 81 4 22 = 25 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 81 4 23 = 19 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 81 4 24 = 71 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 81 4 25 = 61 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 81 4 26 = 41 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 81 4 27 = 1 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 81 4 28 = 47 :=
    slopeOrbit_step_eval 27 6 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 81 4 28 = slopeOrbit 81 4 1
    rw [e28, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 27).filter
        (fun j => canonGap 81 (slopeOrbit 81 4 j) = 4) ⊆ {5} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 5
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(81, 13)`: `23 -> 11 -> 7 -> 31 -> 43 -> 5 -> 79 -> 77 -> 73 -> 65 -> 49 -> 17 -> 55 -> 29 -> 35 -> 59 -> 37 -> 67 -> 53 -> 25 -> 19 -> 71 -> 61 -> 41 -> 1 -> 47 -> 13`, canonical gaps
`2, 3, 4, 2, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3` - period `27`, band-4 count `1` (positions `{3}`). -/
private theorem towerME_cyc_81_13 :
    slopeOrbit 81 13 (1 + 27) = slopeOrbit 81 13 1
      ∧ towerBand4CycleCount 81 13 27 ≤ 1 := by
  have e0 : slopeOrbit 81 13 0 = 13 := rfl
  have e1 : slopeOrbit 81 13 1 = 23 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 81 13 2 = 11 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 81 13 3 = 7 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 81 13 4 = 31 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 81 13 5 = 43 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 81 13 6 = 5 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 81 13 7 = 79 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 81 13 8 = 77 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 81 13 9 = 73 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 81 13 10 = 65 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 81 13 11 = 49 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 81 13 12 = 17 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 81 13 13 = 55 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 81 13 14 = 29 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 81 13 15 = 35 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 81 13 16 = 59 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 81 13 17 = 37 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 81 13 18 = 67 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 81 13 19 = 53 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 81 13 20 = 25 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 81 13 21 = 19 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 81 13 22 = 71 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 81 13 23 = 61 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 81 13 24 = 41 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 81 13 25 = 1 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 81 13 26 = 47 :=
    slopeOrbit_step_eval 25 6 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 81 13 27 = 13 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 81 13 28 = 23 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 81 13 28 = slopeOrbit 81 13 1
    rw [e28, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 27).filter
        (fun j => canonGap 81 (slopeOrbit 81 13 j) = 4) ⊆ {3} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 3
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(81, 40)`: `79 -> 77 -> 73 -> 65 -> 49 -> 17 -> 55 -> 29 -> 35 -> 59 -> 37 -> 67 -> 53 -> 25 -> 19 -> 71 -> 61 -> 41 -> 1 -> 47 -> 13 -> 23 -> 11 -> 7 -> 31 -> 43 -> 5`, canonical gaps
`1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3, 2, 3, 4, 2, 1, 5` - period `27`, band-4 count `1` (positions `{24}`). -/
private theorem towerME_cyc_81_40 :
    slopeOrbit 81 40 (1 + 27) = slopeOrbit 81 40 1
      ∧ towerBand4CycleCount 81 40 27 ≤ 1 := by
  have e0 : slopeOrbit 81 40 0 = 40 := rfl
  have e1 : slopeOrbit 81 40 1 = 79 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 81 40 2 = 77 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 81 40 3 = 73 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 81 40 4 = 65 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 81 40 5 = 49 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 81 40 6 = 17 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 81 40 7 = 55 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 81 40 8 = 29 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 81 40 9 = 35 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 81 40 10 = 59 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 81 40 11 = 37 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 81 40 12 = 67 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 81 40 13 = 53 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 81 40 14 = 25 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 81 40 15 = 19 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 81 40 16 = 71 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 81 40 17 = 61 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 81 40 18 = 41 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 81 40 19 = 1 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 81 40 20 = 47 :=
    slopeOrbit_step_eval 19 6 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 81 40 21 = 13 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 81 40 22 = 23 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 81 40 23 = 11 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 81 40 24 = 7 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 81 40 25 = 31 :=
    slopeOrbit_step_eval 24 3 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 81 40 26 = 43 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 81 40 27 = 5 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 81 40 28 = 79 :=
    slopeOrbit_step_eval 27 4 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 81 40 28 = slopeOrbit 81 40 1
    rw [e28, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 27).filter
        (fun j => canonGap 81 (slopeOrbit 81 40 j) = 4) ⊆ {24} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 24
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(83, 41)`: `81 -> 79 -> 75 -> 67 -> 51 -> 19 -> 69 -> 55 -> 27 -> 25 -> 17 -> 53 -> 23 -> 9 -> 61 -> 39 -> 73 -> 63 -> 43 -> 3 -> 13 -> 21 -> 1 -> 45 -> 7 -> 29 -> 33 -> 49 -> 15 -> 37 -> 65 -> 47 -> 11 -> 5 -> 77 -> 71 -> 59 -> 35 -> 57 -> 31 -> 41`, canonical gaps
`1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3, 2, 7, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2` - period `41`, band-4 count `2` (positions `{14, 25}`). -/
private theorem towerME_cyc_83_41 :
    slopeOrbit 83 41 (1 + 41) = slopeOrbit 83 41 1
      ∧ towerBand4CycleCount 83 41 41 ≤ 2 := by
  have e0 : slopeOrbit 83 41 0 = 41 := rfl
  have e1 : slopeOrbit 83 41 1 = 81 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 83 41 2 = 79 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 83 41 3 = 75 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 83 41 4 = 67 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 83 41 5 = 51 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 83 41 6 = 19 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 83 41 7 = 69 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 83 41 8 = 55 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 83 41 9 = 27 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 83 41 10 = 25 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 83 41 11 = 17 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 83 41 12 = 53 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 83 41 13 = 23 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 83 41 14 = 9 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 83 41 15 = 61 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 83 41 16 = 39 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 83 41 17 = 73 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 83 41 18 = 63 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 83 41 19 = 43 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 83 41 20 = 3 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 83 41 21 = 13 :=
    slopeOrbit_step_eval 20 4 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 83 41 22 = 21 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 83 41 23 = 1 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 83 41 24 = 45 :=
    slopeOrbit_step_eval 23 6 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 83 41 25 = 7 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 83 41 26 = 29 :=
    slopeOrbit_step_eval 25 3 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 83 41 27 = 33 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 83 41 28 = 49 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 83 41 29 = 15 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 83 41 30 = 37 :=
    slopeOrbit_step_eval 29 2 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 83 41 31 = 65 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 83 41 32 = 47 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 83 41 33 = 11 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 83 41 34 = 5 :=
    slopeOrbit_step_eval 33 2 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 83 41 35 = 77 :=
    slopeOrbit_step_eval 34 4 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 83 41 36 = 71 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 83 41 37 = 59 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 83 41 38 = 35 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 83 41 39 = 57 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 83 41 40 = 31 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 83 41 41 = 41 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 83 41 42 = 81 :=
    slopeOrbit_step_eval 41 1 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 83 41 42 = slopeOrbit 83 41 1
    rw [e42, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 41).filter
        (fun j => canonGap 83 (slopeOrbit 83 41 j) = 4) ⊆ {14, 25} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 14 {25}
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 25)
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e28] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e29] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e30] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e31] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e32] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e33] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e34] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e35] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e36] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e37] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e38] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e39] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e40] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e41] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 14 ({25} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(85, 2)`: `43 -> 1`, canonical gaps
`1, 7` - period `2`, band-4-FREE. -/
private theorem towerME_cyc_85_2 :
    slopeOrbit 85 2 (1 + 2) = slopeOrbit 85 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 85 (slopeOrbit 85 2 j) ≠ 4 := by
  have e0 : slopeOrbit 85 2 0 = 2 := rfl
  have e1 : slopeOrbit 85 2 1 = 43 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 85 2 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 85 2 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 85 2 3 = slopeOrbit 85 2 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(85, 8)`: `43 -> 1`, canonical gaps
`1, 7` - period `2`, band-4-FREE. -/
private theorem towerME_cyc_85_8 :
    slopeOrbit 85 8 (1 + 2) = slopeOrbit 85 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 85 (slopeOrbit 85 8 j) ≠ 4 := by
  have e0 : slopeOrbit 85 8 0 = 8 := rfl
  have e1 : slopeOrbit 85 8 1 = 43 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 85 8 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 85 8 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 85 8 3 = slopeOrbit 85 8 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(85, 42)`: `83 -> 81 -> 77 -> 69 -> 53 -> 21`, canonical gaps
`1, 1, 1, 1, 1, 3` - period `6`, band-4-FREE. -/
private theorem towerME_cyc_85_42 :
    slopeOrbit 85 42 (1 + 6) = slopeOrbit 85 42 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 85 (slopeOrbit 85 42 j) ≠ 4 := by
  have e0 : slopeOrbit 85 42 0 = 42 := rfl
  have e1 : slopeOrbit 85 42 1 = 83 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 85 42 2 = 81 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 85 42 3 = 77 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 85 42 4 = 69 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 85 42 5 = 53 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 85 42 6 = 21 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 85 42 7 = 83 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 85 42 7 = slopeOrbit 85 42 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(87, 1)`: `41 -> 77 -> 67 -> 47 -> 7 -> 25 -> 13 -> 17 -> 49 -> 11 -> 1`, canonical gaps
`2, 1, 1, 1, 4, 2, 3, 3, 1, 3, 7` - period `11`, band-4 count `1` (positions `{5}`). -/
private theorem towerME_cyc_87_1 :
    slopeOrbit 87 1 (1 + 11) = slopeOrbit 87 1 1
      ∧ towerBand4CycleCount 87 1 11 ≤ 1 := by
  have e0 : slopeOrbit 87 1 0 = 1 := rfl
  have e1 : slopeOrbit 87 1 1 = 41 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 87 1 2 = 77 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 87 1 3 = 67 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 87 1 4 = 47 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 87 1 5 = 7 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 87 1 6 = 25 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 87 1 7 = 13 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 87 1 8 = 17 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 87 1 9 = 49 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 87 1 10 = 11 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 87 1 11 = 1 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 87 1 12 = 41 :=
    slopeOrbit_step_eval 11 6 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 87 1 12 = slopeOrbit 87 1 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 87 (slopeOrbit 87 1 j) = 4) ⊆ {5} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 5
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(87, 14)`: `25 -> 13 -> 17 -> 49 -> 11 -> 1 -> 41 -> 77 -> 67 -> 47 -> 7`, canonical gaps
`2, 3, 3, 1, 3, 7, 2, 1, 1, 1, 4` - period `11`, band-4 count `1` (positions `{11}`). -/
private theorem towerME_cyc_87_14 :
    slopeOrbit 87 14 (1 + 11) = slopeOrbit 87 14 1
      ∧ towerBand4CycleCount 87 14 11 ≤ 1 := by
  have e0 : slopeOrbit 87 14 0 = 14 := rfl
  have e1 : slopeOrbit 87 14 1 = 25 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 87 14 2 = 13 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 87 14 3 = 17 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 87 14 4 = 49 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 87 14 5 = 11 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 87 14 6 = 1 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 87 14 7 = 41 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 87 14 8 = 77 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 87 14 9 = 67 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 87 14 10 = 47 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 87 14 11 = 7 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 87 14 12 = 25 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 87 14 12 = slopeOrbit 87 14 1
    rw [e12, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 87 (slopeOrbit 87 14 j) = 4) ⊆ {11} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 11
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(87, 43)`: `85 -> 83 -> 79 -> 71 -> 55 -> 23 -> 5 -> 73 -> 59 -> 31 -> 37 -> 61 -> 35 -> 53 -> 19 -> 65 -> 43`, canonical gaps
`1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2` - period `17`, band-4-FREE. -/
private theorem towerME_cyc_87_43 :
    slopeOrbit 87 43 (1 + 17) = slopeOrbit 87 43 1
      ∧ ∀ j, 1 ≤ j → j ≤ 17 → canonGap 87 (slopeOrbit 87 43 j) ≠ 4 := by
  have e0 : slopeOrbit 87 43 0 = 43 := rfl
  have e1 : slopeOrbit 87 43 1 = 85 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 87 43 2 = 83 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 87 43 3 = 79 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 87 43 4 = 71 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 87 43 5 = 55 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 87 43 6 = 23 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 87 43 7 = 5 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 87 43 8 = 73 :=
    slopeOrbit_step_eval 7 4 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 87 43 9 = 59 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 87 43 10 = 31 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 87 43 11 = 37 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 87 43 12 = 61 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 87 43 13 = 35 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 87 43 14 = 53 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 87 43 15 = 19 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 87 43 16 = 65 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 87 43 17 = 43 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 87 43 18 = 85 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 87 43 18 = slopeOrbit 87 43 1
    rw [e18, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)
    · rw [e10]; exact canonGap_ne_four_of_band (by omega)
    · rw [e11]; exact canonGap_ne_four_of_band (by omega)
    · rw [e12]; exact canonGap_ne_four_of_band (by omega)
    · rw [e13]; exact canonGap_ne_four_of_band (by omega)
    · rw [e14]; exact canonGap_ne_four_of_band (by omega)
    · rw [e15]; exact canonGap_ne_four_of_band (by omega)
    · rw [e16]; exact canonGap_ne_four_of_band (by omega)
    · rw [e17]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(89, 44)`: `87 -> 85 -> 81 -> 73 -> 57 -> 25 -> 11`, canonical gaps
`1, 1, 1, 1, 1, 2, 4` - period `7`, band-4 count `1` (positions `{7}`). -/
private theorem towerME_cyc_89_44 :
    slopeOrbit 89 44 (1 + 7) = slopeOrbit 89 44 1
      ∧ towerBand4CycleCount 89 44 7 ≤ 1 := by
  have e0 : slopeOrbit 89 44 0 = 44 := rfl
  have e1 : slopeOrbit 89 44 1 = 87 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 89 44 2 = 85 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 89 44 3 = 81 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 89 44 4 = 73 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 89 44 5 = 57 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 89 44 6 = 25 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 89 44 7 = 11 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 89 44 8 = 87 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 89 44 8 = slopeOrbit 89 44 1
    rw [e8, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 89 (slopeOrbit 89 44 j) = 4) ⊆ {7} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 7
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(91, 3)`: `5 -> 69 -> 47 -> 3`, canonical gaps
`5, 1, 1, 5` - period `4`, band-4-FREE. -/
private theorem towerME_cyc_91_3 :
    slopeOrbit 91 3 (1 + 4) = slopeOrbit 91 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 91 (slopeOrbit 91 3 j) ≠ 4 := by
  have e0 : slopeOrbit 91 3 0 = 3 := rfl
  have e1 : slopeOrbit 91 3 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 91 3 2 = 69 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 91 3 3 = 47 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 91 3 4 = 3 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 91 3 5 = 5 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 91 3 5 = slopeOrbit 91 3 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(91, 6)`: `5 -> 69 -> 47 -> 3`, canonical gaps
`5, 1, 1, 5` - period `4`, band-4-FREE. -/
private theorem towerME_cyc_91_6 :
    slopeOrbit 91 6 (1 + 4) = slopeOrbit 91 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 91 (slopeOrbit 91 6 j) ≠ 4 := by
  have e0 : slopeOrbit 91 6 0 = 6 := rfl
  have e1 : slopeOrbit 91 6 1 = 5 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 91 6 2 = 69 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 91 6 3 = 47 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 91 6 4 = 3 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 91 6 5 = 5 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 91 6 5 = slopeOrbit 91 6 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(91, 45)`: `89 -> 87 -> 83 -> 75 -> 59 -> 27 -> 17 -> 45`, canonical gaps
`1, 1, 1, 1, 1, 2, 3, 2` - period `8`, band-4-FREE. -/
private theorem towerME_cyc_91_45 :
    slopeOrbit 91 45 (1 + 8) = slopeOrbit 91 45 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 → canonGap 91 (slopeOrbit 91 45 j) ≠ 4 := by
  have e0 : slopeOrbit 91 45 0 = 45 := rfl
  have e1 : slopeOrbit 91 45 1 = 89 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 91 45 2 = 87 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 91 45 3 = 83 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 91 45 4 = 75 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 91 45 5 = 59 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 91 45 6 = 27 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 91 45 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 91 45 8 = 45 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 91 45 9 = 89 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 91 45 9 = slopeOrbit 91 45 1
    rw [e9, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(93, 1)`: `35 -> 47 -> 1`, canonical gaps
`2, 1, 7` - period `3`, band-4-FREE. -/
private theorem towerME_cyc_93_1 :
    slopeOrbit 93 1 (1 + 3) = slopeOrbit 93 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 93 (slopeOrbit 93 1 j) ≠ 4 := by
  have e0 : slopeOrbit 93 1 0 = 1 := rfl
  have e1 : slopeOrbit 93 1 1 = 35 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 1 2 = 47 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 93 1 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 93 1 4 = 35 :=
    slopeOrbit_step_eval 3 6 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 1 4 = slopeOrbit 93 1 1
    rw [e4, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(93, 15)`: `27 -> 15`, canonical gaps
`2, 3` - period `2`, band-4-FREE. -/
private theorem towerME_cyc_93_15 :
    slopeOrbit 93 15 (1 + 2) = slopeOrbit 93 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 93 (slopeOrbit 93 15 j) ≠ 4 := by
  have e0 : slopeOrbit 93 15 0 = 15 := rfl
  have e1 : slopeOrbit 93 15 1 = 27 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 15 2 = 15 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 93 15 3 = 27 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 15 3 = slopeOrbit 93 15 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(93, 46)`: `91 -> 89 -> 85 -> 77 -> 61 -> 29 -> 23`, canonical gaps
`1, 1, 1, 1, 1, 2, 3` - period `7`, band-4-FREE. -/
private theorem towerME_cyc_93_46 :
    slopeOrbit 93 46 (1 + 7) = slopeOrbit 93 46 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 93 (slopeOrbit 93 46 j) ≠ 4 := by
  have e0 : slopeOrbit 93 46 0 = 46 := rfl
  have e1 : slopeOrbit 93 46 1 = 91 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 46 2 = 89 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 93 46 3 = 85 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 93 46 4 = 77 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 93 46 5 = 61 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 93 46 6 = 29 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 93 46 7 = 23 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 93 46 8 = 91 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 46 8 = slopeOrbit 93 46 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(95, 2)`: `33 -> 37 -> 53 -> 11 -> 81 -> 67 -> 39 -> 61 -> 27 -> 13 -> 9 -> 49 -> 3 -> 1`, canonical gaps
`2, 2, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 5, 7` - period `14`, band-4 count `2` (positions `{4, 11}`). -/
private theorem towerME_cyc_95_2 :
    slopeOrbit 95 2 (1 + 14) = slopeOrbit 95 2 1
      ∧ towerBand4CycleCount 95 2 14 ≤ 2 := by
  have e0 : slopeOrbit 95 2 0 = 2 := rfl
  have e1 : slopeOrbit 95 2 1 = 33 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 95 2 2 = 37 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 95 2 3 = 53 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 95 2 4 = 11 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 95 2 5 = 81 :=
    slopeOrbit_step_eval 4 3 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 95 2 6 = 67 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 95 2 7 = 39 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 95 2 8 = 61 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 95 2 9 = 27 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 95 2 10 = 13 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 95 2 11 = 9 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 95 2 12 = 49 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 95 2 13 = 3 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 95 2 14 = 1 :=
    slopeOrbit_step_eval 13 4 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 95 2 15 = 33 :=
    slopeOrbit_step_eval 14 6 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 95 2 15 = slopeOrbit 95 2 1
    rw [e15, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 14).filter
        (fun j => canonGap 95 (slopeOrbit 95 2 j) = 4) ⊆ {4, 11} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 4 {11}
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 11)
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 4 ({11} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(95, 9)`: `49 -> 3 -> 1 -> 33 -> 37 -> 53 -> 11 -> 81 -> 67 -> 39 -> 61 -> 27 -> 13 -> 9`, canonical gaps
`1, 5, 7, 2, 2, 1, 4, 1, 1, 2, 1, 2, 3, 4` - period `14`, band-4 count `2` (positions `{7, 14}`). -/
private theorem towerME_cyc_95_9 :
    slopeOrbit 95 9 (1 + 14) = slopeOrbit 95 9 1
      ∧ towerBand4CycleCount 95 9 14 ≤ 2 := by
  have e0 : slopeOrbit 95 9 0 = 9 := rfl
  have e1 : slopeOrbit 95 9 1 = 49 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 95 9 2 = 3 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 95 9 3 = 1 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 95 9 4 = 33 :=
    slopeOrbit_step_eval 3 6 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 95 9 5 = 37 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 95 9 6 = 53 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 95 9 7 = 11 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 95 9 8 = 81 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 95 9 9 = 67 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 95 9 10 = 39 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 95 9 11 = 61 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 95 9 12 = 27 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 95 9 13 = 13 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 95 9 14 = 9 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 95 9 15 = 49 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 95 9 15 = slopeOrbit 95 9 1
    rw [e15, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 14).filter
        (fun j => canonGap 95 (slopeOrbit 95 9 j) = 4) ⊆ {7, 14} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 7 {14}
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 14)
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 7 ({14} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(95, 47)`: `93 -> 91 -> 87 -> 79 -> 63 -> 31 -> 29 -> 21 -> 73 -> 51 -> 7 -> 17 -> 41 -> 69 -> 43 -> 77 -> 59 -> 23 -> 89 -> 83 -> 71 -> 47`, canonical gaps
`1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2` - period `22`, band-4 count `1` (positions `{11}`). -/
private theorem towerME_cyc_95_47 :
    slopeOrbit 95 47 (1 + 22) = slopeOrbit 95 47 1
      ∧ towerBand4CycleCount 95 47 22 ≤ 1 := by
  have e0 : slopeOrbit 95 47 0 = 47 := rfl
  have e1 : slopeOrbit 95 47 1 = 93 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 95 47 2 = 91 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 95 47 3 = 87 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 95 47 4 = 79 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 95 47 5 = 63 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 95 47 6 = 31 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 95 47 7 = 29 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 95 47 8 = 21 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 95 47 9 = 73 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 95 47 10 = 51 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 95 47 11 = 7 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 95 47 12 = 17 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 95 47 13 = 41 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 95 47 14 = 69 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 95 47 15 = 43 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 95 47 16 = 77 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 95 47 17 = 59 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 95 47 18 = 23 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 95 47 19 = 89 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 95 47 20 = 83 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 95 47 21 = 71 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 95 47 22 = 47 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 95 47 23 = 93 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 95 47 23 = slopeOrbit 95 47 1
    rw [e23, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 22).filter
        (fun j => canonGap 95 (slopeOrbit 95 47 j) = 4) ⊆ {11} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 11
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(97, 48)`: `95 -> 93 -> 89 -> 81 -> 65 -> 33 -> 35 -> 43 -> 75 -> 53 -> 9 -> 47 -> 91 -> 85 -> 73 -> 49 -> 1 -> 31 -> 27 -> 11 -> 79 -> 61 -> 25 -> 3`, canonical gaps
`1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2, 2, 4, 1, 1, 2, 6` - period `24`, band-4 count `2` (positions `{11, 20}`). -/
private theorem towerME_cyc_97_48 :
    slopeOrbit 97 48 (1 + 24) = slopeOrbit 97 48 1
      ∧ towerBand4CycleCount 97 48 24 ≤ 2 := by
  have e0 : slopeOrbit 97 48 0 = 48 := rfl
  have e1 : slopeOrbit 97 48 1 = 95 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 97 48 2 = 93 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 97 48 3 = 89 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 97 48 4 = 81 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 97 48 5 = 65 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 97 48 6 = 33 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 97 48 7 = 35 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 97 48 8 = 43 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 97 48 9 = 75 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 97 48 10 = 53 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 97 48 11 = 9 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 97 48 12 = 47 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 97 48 13 = 91 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 97 48 14 = 85 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 97 48 15 = 73 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 97 48 16 = 49 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 97 48 17 = 1 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 97 48 18 = 31 :=
    slopeOrbit_step_eval 17 6 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 97 48 19 = 27 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 97 48 20 = 11 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 97 48 21 = 79 :=
    slopeOrbit_step_eval 20 3 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 97 48 22 = 61 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 97 48 23 = 25 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 97 48 24 = 3 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 97 48 25 = 95 :=
    slopeOrbit_step_eval 24 5 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 97 48 25 = slopeOrbit 97 48 1
    rw [e25, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 24).filter
        (fun j => canonGap 97 (slopeOrbit 97 48 j) = 4) ⊆ {11, 20} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 11 {20}
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 20)
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le 11 ({20} : Finset ℕ)
    rw [Finset.card_singleton] at hins
    omega

/-- Orbit cycle for `(99, 1)`: `29 -> 17 -> 37 -> 49 -> 97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1`, canonical gaps
`2, 3, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7` - period `15`, band-4-FREE. -/
private theorem towerME_cyc_99_1 :
    slopeOrbit 99 1 (1 + 15) = slopeOrbit 99 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 15 → canonGap 99 (slopeOrbit 99 1 j) ≠ 4 := by
  have e0 : slopeOrbit 99 1 0 = 1 := rfl
  have e1 : slopeOrbit 99 1 1 = 29 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 99 1 2 = 17 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 99 1 3 = 37 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 99 1 4 = 49 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 99 1 5 = 97 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 99 1 6 = 95 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 99 1 7 = 91 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 99 1 8 = 83 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 99 1 9 = 67 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 99 1 10 = 35 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 99 1 11 = 41 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 99 1 12 = 65 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 99 1 13 = 31 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 99 1 14 = 25 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 99 1 15 = 1 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 99 1 16 = 29 :=
    slopeOrbit_step_eval 15 6 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 99 1 16 = slopeOrbit 99 1 1
    rw [e16, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)
    · rw [e10]; exact canonGap_ne_four_of_band (by omega)
    · rw [e11]; exact canonGap_ne_four_of_band (by omega)
    · rw [e12]; exact canonGap_ne_four_of_band (by omega)
    · rw [e13]; exact canonGap_ne_four_of_band (by omega)
    · rw [e14]; exact canonGap_ne_four_of_band (by omega)
    · rw [e15]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(99, 4)`: `29 -> 17 -> 37 -> 49 -> 97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1`, canonical gaps
`2, 3, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7` - period `15`, band-4-FREE. -/
private theorem towerME_cyc_99_4 :
    slopeOrbit 99 4 (1 + 15) = slopeOrbit 99 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 15 → canonGap 99 (slopeOrbit 99 4 j) ≠ 4 := by
  have e0 : slopeOrbit 99 4 0 = 4 := rfl
  have e1 : slopeOrbit 99 4 1 = 29 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 99 4 2 = 17 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 99 4 3 = 37 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 99 4 4 = 49 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 99 4 5 = 97 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 99 4 6 = 95 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 99 4 7 = 91 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 99 4 8 = 83 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 99 4 9 = 67 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 99 4 10 = 35 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 99 4 11 = 41 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 99 4 12 = 65 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 99 4 13 = 31 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 99 4 14 = 25 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 99 4 15 = 1 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 99 4 16 = 29 :=
    slopeOrbit_step_eval 15 6 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 99 4 16 = slopeOrbit 99 4 1
    rw [e16, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)
    · rw [e10]; exact canonGap_ne_four_of_band (by omega)
    · rw [e11]; exact canonGap_ne_four_of_band (by omega)
    · rw [e12]; exact canonGap_ne_four_of_band (by omega)
    · rw [e13]; exact canonGap_ne_four_of_band (by omega)
    · rw [e14]; exact canonGap_ne_four_of_band (by omega)
    · rw [e15]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(99, 5)`: `61 -> 23 -> 85 -> 71 -> 43 -> 73 -> 47 -> 89 -> 79 -> 59 -> 19 -> 53 -> 7 -> 13 -> 5`, canonical gaps
`1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5` - period `15`, band-4 count `1` (positions `{13}`). -/
private theorem towerME_cyc_99_5 :
    slopeOrbit 99 5 (1 + 15) = slopeOrbit 99 5 1
      ∧ towerBand4CycleCount 99 5 15 ≤ 1 := by
  have e0 : slopeOrbit 99 5 0 = 5 := rfl
  have e1 : slopeOrbit 99 5 1 = 61 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 99 5 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 99 5 3 = 85 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 99 5 4 = 71 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 99 5 5 = 43 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 99 5 6 = 73 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 99 5 7 = 47 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 99 5 8 = 89 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 99 5 9 = 79 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 99 5 10 = 59 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 99 5 11 = 19 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 99 5 12 = 53 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 99 5 13 = 7 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 99 5 14 = 13 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 99 5 15 = 5 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 99 5 16 = 61 :=
    slopeOrbit_step_eval 15 4 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 99 5 16 = slopeOrbit 99 5 1
    rw [e16, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 15).filter
        (fun j => canonGap 99 (slopeOrbit 99 5 j) = 4) ⊆ {13} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 13
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-- Orbit cycle for `(99, 16)`: `29 -> 17 -> 37 -> 49 -> 97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1`, canonical gaps
`2, 3, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7` - period `15`, band-4-FREE. -/
private theorem towerME_cyc_99_16 :
    slopeOrbit 99 16 (1 + 15) = slopeOrbit 99 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 15 → canonGap 99 (slopeOrbit 99 16 j) ≠ 4 := by
  have e0 : slopeOrbit 99 16 0 = 16 := rfl
  have e1 : slopeOrbit 99 16 1 = 29 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 99 16 2 = 17 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 99 16 3 = 37 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 99 16 4 = 49 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 99 16 5 = 97 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 99 16 6 = 95 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 99 16 7 = 91 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 99 16 8 = 83 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 99 16 9 = 67 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 99 16 10 = 35 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 99 16 11 = 41 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 99 16 12 = 65 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 99 16 13 = 31 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 99 16 14 = 25 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 99 16 15 = 1 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 99 16 16 = 29 :=
    slopeOrbit_step_eval 15 6 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 99 16 16 = slopeOrbit 99 16 1
    rw [e16, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)
    · rw [e10]; exact canonGap_ne_four_of_band (by omega)
    · rw [e11]; exact canonGap_ne_four_of_band (by omega)
    · rw [e12]; exact canonGap_ne_four_of_band (by omega)
    · rw [e13]; exact canonGap_ne_four_of_band (by omega)
    · rw [e14]; exact canonGap_ne_four_of_band (by omega)
    · rw [e15]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(99, 49)`: `97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1 -> 29 -> 17 -> 37 -> 49`, canonical gaps
`1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2, 3, 2, 2` - period `15`, band-4-FREE. -/
private theorem towerME_cyc_99_49 :
    slopeOrbit 99 49 (1 + 15) = slopeOrbit 99 49 1
      ∧ ∀ j, 1 ≤ j → j ≤ 15 → canonGap 99 (slopeOrbit 99 49 j) ≠ 4 := by
  have e0 : slopeOrbit 99 49 0 = 49 := rfl
  have e1 : slopeOrbit 99 49 1 = 97 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 99 49 2 = 95 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 99 49 3 = 91 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 99 49 4 = 83 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 99 49 5 = 67 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 99 49 6 = 35 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 99 49 7 = 41 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 99 49 8 = 65 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 99 49 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 99 49 10 = 25 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 99 49 11 = 1 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 99 49 12 = 29 :=
    slopeOrbit_step_eval 11 6 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 99 49 13 = 17 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 99 49 14 = 37 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 99 49 15 = 49 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 99 49 16 = 97 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 99 49 16 = slopeOrbit 99 49 1
    rw [e16, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)
    · rw [e10]; exact canonGap_ne_four_of_band (by omega)
    · rw [e11]; exact canonGap_ne_four_of_band (by omega)
    · rw [e12]; exact canonGap_ne_four_of_band (by omega)
    · rw [e13]; exact canonGap_ne_four_of_band (by omega)
    · rw [e14]; exact canonGap_ne_four_of_band (by omega)
    · rw [e15]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(101, 50)`: `99 -> 97 -> 93 -> 85 -> 69 -> 37 -> 47 -> 87 -> 73 -> 45 -> 79 -> 57 -> 13 -> 3 -> 91 -> 81 -> 61 -> 21 -> 67 -> 33 -> 31 -> 23 -> 83 -> 65 -> 29 -> 15 -> 19 -> 51 -> 1 -> 27 -> 7 -> 11 -> 75 -> 49 -> 95 -> 89 -> 77 -> 53 -> 5 -> 59 -> 17 -> 35 -> 39 -> 55 -> 9 -> 43 -> 71 -> 41 -> 63 -> 25`, canonical gaps
`1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 7, 2, 4, 4, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 3` - period `50`, band-4 count `3` (positions `{31, 32, 45}`). -/
private theorem towerME_cyc_101_50 :
    slopeOrbit 101 50 (1 + 50) = slopeOrbit 101 50 1
      ∧ towerBand4CycleCount 101 50 50 ≤ 3 := by
  have e0 : slopeOrbit 101 50 0 = 50 := rfl
  have e1 : slopeOrbit 101 50 1 = 99 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 101 50 2 = 97 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 101 50 3 = 93 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 101 50 4 = 85 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 101 50 5 = 69 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 101 50 6 = 37 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 101 50 7 = 47 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 101 50 8 = 87 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 101 50 9 = 73 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 101 50 10 = 45 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 101 50 11 = 79 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 101 50 12 = 57 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 101 50 13 = 13 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 101 50 14 = 3 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 101 50 15 = 91 :=
    slopeOrbit_step_eval 14 5 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 101 50 16 = 81 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 101 50 17 = 61 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 101 50 18 = 21 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 101 50 19 = 67 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 101 50 20 = 33 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 101 50 21 = 31 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 101 50 22 = 23 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 101 50 23 = 83 :=
    slopeOrbit_step_eval 22 2 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 101 50 24 = 65 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 101 50 25 = 29 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 101 50 26 = 15 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 101 50 27 = 19 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 101 50 28 = 51 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 101 50 29 = 1 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 101 50 30 = 27 :=
    slopeOrbit_step_eval 29 6 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 101 50 31 = 7 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 101 50 32 = 11 :=
    slopeOrbit_step_eval 31 3 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 101 50 33 = 75 :=
    slopeOrbit_step_eval 32 3 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 101 50 34 = 49 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 101 50 35 = 95 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 101 50 36 = 89 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 101 50 37 = 77 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 101 50 38 = 53 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 101 50 39 = 5 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 101 50 40 = 59 :=
    slopeOrbit_step_eval 39 4 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 101 50 41 = 17 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 101 50 42 = 35 :=
    slopeOrbit_step_eval 41 2 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 101 50 43 = 39 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 101 50 44 = 55 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 101 50 45 = 9 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 101 50 46 = 43 :=
    slopeOrbit_step_eval 45 3 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 101 50 47 = 71 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 101 50 48 = 41 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 101 50 49 = 63 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 101 50 50 = 25 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 101 50 51 = 99 :=
    slopeOrbit_step_eval 50 2 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 101 50 51 = slopeOrbit 101 50 1
    rw [e51, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 50).filter
        (fun j => canonGap 101 (slopeOrbit 101 50 j) = 4) ⊆ {31, 32, 45} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e20] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e28] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e29] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e30] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_self 31 {32, 45}
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self 32 {45})
      · rw [e33] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e34] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e35] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e36] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e37] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e38] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e39] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e40] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e41] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e42] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e43] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e44] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self 45))
      · rw [e46] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e47] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e48] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e49] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e50] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    have hins1 := Finset.card_insert_le 31 ({32, 45} : Finset ℕ)
    have hins2 := Finset.card_insert_le 32 ({45} : Finset ℕ)
    rw [Finset.card_singleton] at hins2
    omega

/-- Orbit cycle for `(103, 51)`: `101 -> 99 -> 95 -> 87 -> 71 -> 39 -> 53 -> 3 -> 89 -> 75 -> 47 -> 85 -> 67 -> 31 -> 21 -> 65 -> 27 -> 5 -> 57 -> 11 -> 73 -> 43 -> 69 -> 35 -> 37 -> 45 -> 77 -> 51`, canonical gaps
`1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2` - period `28`, band-4 count `1` (positions `{20}`). -/
private theorem towerME_cyc_103_51 :
    slopeOrbit 103 51 (1 + 28) = slopeOrbit 103 51 1
      ∧ towerBand4CycleCount 103 51 28 ≤ 1 := by
  have e0 : slopeOrbit 103 51 0 = 51 := rfl
  have e1 : slopeOrbit 103 51 1 = 101 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 103 51 2 = 99 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 103 51 3 = 95 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 103 51 4 = 87 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 103 51 5 = 71 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 103 51 6 = 39 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 103 51 7 = 53 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 103 51 8 = 3 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 103 51 9 = 89 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 103 51 10 = 75 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 103 51 11 = 47 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 103 51 12 = 85 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 103 51 13 = 67 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 103 51 14 = 31 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 103 51 15 = 21 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 103 51 16 = 65 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 103 51 17 = 27 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 103 51 18 = 5 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 103 51 19 = 57 :=
    slopeOrbit_step_eval 18 4 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 103 51 20 = 11 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 103 51 21 = 73 :=
    slopeOrbit_step_eval 20 3 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 103 51 22 = 43 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 103 51 23 = 69 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 103 51 24 = 35 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 103 51 25 = 37 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 103 51 26 = 45 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 103 51 27 = 77 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 103 51 28 = 51 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 103 51 29 = 101 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · show slopeOrbit 103 51 29 = slopeOrbit 103 51 1
    rw [e29, e1]
  · unfold towerBand4CycleCount
    have hsub : (Finset.Icc 1 28).filter
        (fun j => canonGap 103 (slopeOrbit 103 51 j) = 4) ⊆ {20} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · rw [e1] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e2] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e3] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e4] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e5] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e6] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e7] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e8] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e9] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e10] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e11] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e12] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e13] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e14] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e15] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e16] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e17] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e18] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e19] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · exact Finset.mem_singleton_self 20
      · rw [e21] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e22] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e23] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e24] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e25] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e26] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e27] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
      · rw [e28] at hband
        exact absurd hband (canonGap_ne_four_of_band (by omega))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    exact hcard

/-! ## Part 4.  The band-4-free closures: per-datum fibre emptiness -/

/-- `(27, 1)` rides the band-4-free cycle `5 -> 13 -> 25 -> 23 -> 19 -> 11 -> 17 -> 7 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_27_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_27_1.1 towerME_cyc_27_1.2

/-- `(27, 4)` rides the band-4-free cycle `5 -> 13 -> 25 -> 23 -> 19 -> 11 -> 17 -> 7 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_27_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_27_4.1 towerME_cyc_27_4.2

/-- `(27, 13)` rides the band-4-free cycle `25 -> 23 -> 19 -> 11 -> 17 -> 7 -> 1 -> 5 -> 13` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_27_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 13) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_27_13.1 towerME_cyc_27_13.2

/-- `(31, 15)` rides the band-4-free cycle `29 -> 27 -> 23 -> 15` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_31_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) (hK : (class1SlopeDatum ctx).K₀ = 15) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_31_15.1 towerME_cyc_31_15.2

/-- `(33, 1)` rides the band-4-free cycle `31 -> 29 -> 25 -> 17 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_33_1.1 towerME_cyc_33_1.2

/-- `(33, 5)` rides the band-4-free cycle `7 -> 23 -> 13 -> 19 -> 5` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_33_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_33_5.1 towerME_cyc_33_5.2

/-- `(33, 16)` rides the band-4-free cycle `31 -> 29 -> 25 -> 17 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_33_16.1 towerME_cyc_33_16.2

/-- `(35, 2)` rides the band-4-free cycle `29 -> 23 -> 11 -> 9 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_35_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_35_2.1 towerME_cyc_35_2.2

/-- `(39, 1)` rides the band-4-free cycle `25 -> 11 -> 5 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_39_1.1 towerME_cyc_39_1.2

/-- `(39, 19)` rides the band-4-free cycle `37 -> 35 -> 31 -> 23 -> 7 -> 17 -> 29 -> 19` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_39_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 19) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_39_19.1 towerME_cyc_39_19.2

/-- `(43, 21)` rides the band-4-free cycle `41 -> 39 -> 35 -> 27 -> 11 -> 1 -> 21` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_43_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) (hK : (class1SlopeDatum ctx).K₀ = 21) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_43_21.1 towerME_cyc_43_21.2

/-- `(45, 1)` rides the band-4-free cycle `19 -> 31 -> 17 -> 23 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_45_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_45_1.1 towerME_cyc_45_1.2

/-- `(45, 2)` rides the band-4-free cycle `19 -> 31 -> 17 -> 23 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_45_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_45_2.1 towerME_cyc_45_2.2

/-- `(45, 4)` rides the band-4-free cycle `19 -> 31 -> 17 -> 23 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_45_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_45_4.1 towerME_cyc_45_4.2

/-- `(45, 7)` rides the band-4-free cycle `11 -> 43 -> 41 -> 37 -> 29 -> 13 -> 7` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_45_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_45_7.1 towerME_cyc_45_7.2

/-- `(45, 22)` rides the band-4-free cycle `43 -> 41 -> 37 -> 29 -> 13 -> 7 -> 11` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_45_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 22) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_45_22.1 towerME_cyc_45_22.2

/-- `(51, 1)` rides the band-4-free cycle `13 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_51_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_51_1.1 towerME_cyc_51_1.2

/-- `(51, 8)` rides the band-4-free cycle `13 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_51_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_51_8.1 towerME_cyc_51_8.2

/-- `(51, 25)` rides the band-4-free cycle `49 -> 47 -> 43 -> 35 -> 19 -> 25` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_51_25 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 25) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_51_25.1 towerME_cyc_51_25.2

/-- `(55, 2)` rides the band-4-free cycle `9 -> 17 -> 13 -> 49 -> 43 -> 31 -> 7 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_55_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_55_2.1 towerME_cyc_55_2.2

/-- `(55, 27)` rides the band-4-free cycle `53 -> 51 -> 47 -> 39 -> 23 -> 37 -> 19 -> 21 -> 29 -> 3 -> 41 -> 27` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_55_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 27) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_55_27.1 towerME_cyc_55_27.2

/-- `(57, 9)` rides the band-4-free cycle `15 -> 3 -> 39 -> 21 -> 27 -> 51 -> 45 -> 33 -> 9` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_57_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 9) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_57_9.1 towerME_cyc_57_9.2

/-- `(63, 1)` rides the band-4-free cycle `1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_63_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_63_1.1 towerME_cyc_63_1.2

/-- `(63, 3)` rides the band-4-free cycle `33 -> 3` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_63_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_63_3.1 towerME_cyc_63_3.2

/-- `(63, 4)` rides the band-4-free cycle `1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_63_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_63_4.1 towerME_cyc_63_4.2

/-- `(63, 31)` rides the band-4-free cycle `61 -> 59 -> 55 -> 47 -> 31` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_63_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 31) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_63_31.1 towerME_cyc_63_31.2

/-- `(65, 2)` rides the band-4-free cycle `63 -> 61 -> 57 -> 49 -> 33 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_65_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_65_2.1 towerME_cyc_65_2.2

/-- `(65, 6)` rides the band-4-free cycle `31 -> 59 -> 53 -> 41 -> 17 -> 3` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_65_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_65_6.1 towerME_cyc_65_6.2

/-- `(65, 32)` rides the band-4-free cycle `63 -> 61 -> 57 -> 49 -> 33 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_65_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) (hK : (class1SlopeDatum ctx).K₀ = 32) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_65_32.1 towerME_cyc_65_32.2

/-- `(69, 1)` rides the band-4-free cycle `59 -> 49 -> 29 -> 47 -> 25 -> 31 -> 55 -> 41 -> 13 -> 35 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_69_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_69_1.1 towerME_cyc_69_1.2

/-- `(75, 1)` rides the band-4-free cycle `53 -> 31 -> 49 -> 23 -> 17 -> 61 -> 47 -> 19 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_75_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_75_1.1 towerME_cyc_75_1.2

/-- `(75, 2)` rides the band-4-free cycle `53 -> 31 -> 49 -> 23 -> 17 -> 61 -> 47 -> 19 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_75_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_75_2.1 towerME_cyc_75_2.2

/-- `(85, 2)` rides the band-4-free cycle `43 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_85_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_85_2.1 towerME_cyc_85_2.2

/-- `(85, 8)` rides the band-4-free cycle `43 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_85_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_85_8.1 towerME_cyc_85_8.2

/-- `(85, 42)` rides the band-4-free cycle `83 -> 81 -> 77 -> 69 -> 53 -> 21` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_85_42 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) (hK : (class1SlopeDatum ctx).K₀ = 42) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_85_42.1 towerME_cyc_85_42.2

/-- `(87, 43)` rides the band-4-free cycle `85 -> 83 -> 79 -> 71 -> 55 -> 23 -> 5 -> 73 -> 59 -> 31 -> 37 -> 61 -> 35 -> 53 -> 19 -> 65 -> 43` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_87_43 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 43) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_87_43.1 towerME_cyc_87_43.2

/-- `(91, 3)` rides the band-4-free cycle `5 -> 69 -> 47 -> 3` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_91_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_91_3.1 towerME_cyc_91_3.2

/-- `(91, 6)` rides the band-4-free cycle `5 -> 69 -> 47 -> 3` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_91_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_91_6.1 towerME_cyc_91_6.2

/-- `(91, 45)` rides the band-4-free cycle `89 -> 87 -> 83 -> 75 -> 59 -> 27 -> 17 -> 45` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_91_45 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) (hK : (class1SlopeDatum ctx).K₀ = 45) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_91_45.1 towerME_cyc_91_45.2

/-- `(93, 1)` rides the band-4-free cycle `35 -> 47 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_93_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_93_1.1 towerME_cyc_93_1.2

/-- `(93, 15)` rides the band-4-free cycle `27 -> 15` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_93_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) (hK : (class1SlopeDatum ctx).K₀ = 15) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_93_15.1 towerME_cyc_93_15.2

/-- `(93, 46)` rides the band-4-free cycle `91 -> 89 -> 85 -> 77 -> 61 -> 29 -> 23` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_93_46 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) (hK : (class1SlopeDatum ctx).K₀ = 46) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_93_46.1 towerME_cyc_93_46.2

/-- `(99, 1)` rides the band-4-free cycle `29 -> 17 -> 37 -> 49 -> 97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_99_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_99_1.1 towerME_cyc_99_1.2

/-- `(99, 4)` rides the band-4-free cycle `29 -> 17 -> 37 -> 49 -> 97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_99_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_99_4.1 towerME_cyc_99_4.2

/-- `(99, 16)` rides the band-4-free cycle `29 -> 17 -> 37 -> 49 -> 97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_99_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_99_16.1 towerME_cyc_99_16.2

/-- `(99, 49)` rides the band-4-free cycle `97 -> 95 -> 91 -> 83 -> 67 -> 35 -> 41 -> 65 -> 31 -> 25 -> 1 -> 29 -> 17 -> 37 -> 49` - the class-2
routed fibre is EMPTY on every shell with this datum. -/
theorem towerME_empty_99_49 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 49) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ :=
  class2Fibre_empty_of_collision_free ctx hq hK (by norm_num)
    towerME_cyc_99_49.1 towerME_cyc_99_49.2

/-! ## Part 5.  Ten whole moduli close completely (every admissible `K0` is free) -/

/-- **The whole modulus `q = 27` closes**: every pin-admissible
`K0 in {1, 4, 13}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 27` shell, with no residual demand. -/
theorem towerME_empty_mod_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_27 ctx hq with hv | hv | hv
  · exact towerME_empty_27_1 ctx hq hv
  · exact towerME_empty_27_4 ctx hq hv
  · exact towerME_empty_27_13 ctx hq hv

/-- **The whole modulus `q = 31` closes**: every pin-admissible
`K0 in {15}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 31` shell, with no residual demand. -/
theorem towerME_empty_mod_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  have hv := towerME_pin_31 ctx hq
  exact towerME_empty_31_15 ctx hq hv

/-- **The whole modulus `q = 33` closes**: every pin-admissible
`K0 in {1, 5, 16}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 33` shell, with no residual demand. -/
theorem towerME_empty_mod_33 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_33 ctx hq with hv | hv | hv
  · exact towerME_empty_33_1 ctx hq hv
  · exact towerME_empty_33_5 ctx hq hv
  · exact towerME_empty_33_16 ctx hq hv

/-- **The whole modulus `q = 43` closes**: every pin-admissible
`K0 in {21}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 43` shell, with no residual demand. -/
theorem towerME_empty_mod_43 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  have hv := towerME_pin_43 ctx hq
  exact towerME_empty_43_21 ctx hq hv

/-- **The whole modulus `q = 45` closes**: every pin-admissible
`K0 in {1, 2, 4, 7, 22}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 45` shell, with no residual demand. -/
theorem towerME_empty_mod_45 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_45 ctx hq with hv | hv | hv | hv | hv
  · exact towerME_empty_45_1 ctx hq hv
  · exact towerME_empty_45_2 ctx hq hv
  · exact towerME_empty_45_4 ctx hq hv
  · exact towerME_empty_45_7 ctx hq hv
  · exact towerME_empty_45_22 ctx hq hv

/-- **The whole modulus `q = 51` closes**: every pin-admissible
`K0 in {1, 8, 25}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 51` shell, with no residual demand. -/
theorem towerME_empty_mod_51 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_51 ctx hq with hv | hv | hv
  · exact towerME_empty_51_1 ctx hq hv
  · exact towerME_empty_51_8 ctx hq hv
  · exact towerME_empty_51_25 ctx hq hv

/-- **The whole modulus `q = 65` closes**: every pin-admissible
`K0 in {2, 6, 32}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 65` shell, with no residual demand. -/
theorem towerME_empty_mod_65 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_65 ctx hq with hv | hv | hv
  · exact towerME_empty_65_2 ctx hq hv
  · exact towerME_empty_65_6 ctx hq hv
  · exact towerME_empty_65_32 ctx hq hv

/-- **The whole modulus `q = 85` closes**: every pin-admissible
`K0 in {2, 8, 42}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 85` shell, with no residual demand. -/
theorem towerME_empty_mod_85 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_85 ctx hq with hv | hv | hv
  · exact towerME_empty_85_2 ctx hq hv
  · exact towerME_empty_85_8 ctx hq hv
  · exact towerME_empty_85_42 ctx hq hv

/-- **The whole modulus `q = 91` closes**: every pin-admissible
`K0 in {3, 6, 45}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 91` shell, with no residual demand. -/
theorem towerME_empty_mod_91 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_91 ctx hq with hv | hv | hv
  · exact towerME_empty_91_3 ctx hq hv
  · exact towerME_empty_91_6 ctx hq hv
  · exact towerME_empty_91_45 ctx hq hv

/-- **The whole modulus `q = 93` closes**: every pin-admissible
`K0 in {1, 15, 46}` rides a band-4-free cycle - the class-2 fibre is
EMPTY on every `q = 93` shell, with no residual demand. -/
theorem towerME_empty_mod_93 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerME_pin_93 ctx hq with hv | hv | hv
  · exact towerME_empty_93_1 ctx hq hv
  · exact towerME_empty_93_15 ctx hq hv
  · exact towerME_empty_93_46 ctx hq hv

/-! ## Part 6.  The counted closures: per-`(q, K0)` cycle-inequality thresholds -/

/-- **The `(25, 2)` counted closure**: period `10`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 9` (and window `K >= 22`). -/
theorem towerME_ineq_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hm : towerSparsityBlock ctx ≤ 9) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_25_2.1 towerME_cyc_25_2.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(25, 12)` counted closure**: period `10`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 9` (and window `K >= 22`). -/
theorem towerME_ineq_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hm : towerSparsityBlock ctx ≤ 9) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_25_12.1 towerME_cyc_25_12.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(29, 14)` counted closure**: period `14`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 13` (and window `K >= 22`). -/
theorem towerME_ineq_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hm : towerSparsityBlock ctx ≤ 13) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_29_14.1 towerME_cyc_29_14.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(35, 3)` counted closure**: period `7`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 6` (and window `K >= 22`). -/
theorem towerME_ineq_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hm : towerSparsityBlock ctx ≤ 6) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_35_3.1 towerME_cyc_35_3.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(35, 17)` counted closure**: period `7`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 6` (and window `K >= 22`). -/
theorem towerME_ineq_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hm : towerSparsityBlock ctx ≤ 6) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_35_17.1 towerME_cyc_35_17.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(37, 18)` counted closure**: period `18`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 17` (and window `K >= 22`). -/
theorem towerME_ineq_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (hm : towerSparsityBlock ctx ≤ 17) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_37_18.1 towerME_cyc_37_18.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(39, 6)` counted closure**: period `6`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 5` (and window `K >= 22`). -/
theorem towerME_ineq_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6)
    (hm : towerSparsityBlock ctx ≤ 5) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_39_6.1 towerME_cyc_39_6.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(41, 20)` counted closure**: period `10`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 9` (and window `K >= 22`). -/
theorem towerME_ineq_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    (hm : towerSparsityBlock ctx ≤ 9) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_41_20.1 towerME_cyc_41_20.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(47, 23)` counted closure**: period `14`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 13` (and window `K >= 22`). -/
theorem towerME_ineq_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23)
    (hm : towerSparsityBlock ctx ≤ 13) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_47_23.1 towerME_cyc_47_23.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(49, 3)` counted closure**: period `11`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 10` (and window `K >= 22`). -/
theorem towerME_ineq_49_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hm : towerSparsityBlock ctx ≤ 10) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_49_3.1 towerME_cyc_49_3.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(49, 24)` counted closure**: period `11`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 10` (and window `K >= 22`). -/
theorem towerME_ineq_49_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24)
    (hm : towerSparsityBlock ctx ≤ 10) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_49_24.1 towerME_cyc_49_24.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(53, 26)` counted closure**: period `26`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 24` (and window `K >= 22`). -/
theorem towerME_ineq_53_26 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 53) (hK : (class1SlopeDatum ctx).K₀ = 26)
    (hm : towerSparsityBlock ctx ≤ 24) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_53_26.1 towerME_cyc_53_26.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(55, 5)` counted closure**: period `5`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 4` (and window `K >= 22`). -/
theorem towerME_ineq_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hm : towerSparsityBlock ctx ≤ 4) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_55_5.1 towerME_cyc_55_5.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(57, 1)` counted closure**: period `9`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 8` (and window `K >= 22`). -/
theorem towerME_ineq_57_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hm : towerSparsityBlock ctx ≤ 8) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_57_1.1 towerME_cyc_57_1.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(57, 28)` counted closure**: period `9`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 8` (and window `K >= 22`). -/
theorem towerME_ineq_57_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28)
    (hm : towerSparsityBlock ctx ≤ 8) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_57_28.1 towerME_cyc_57_28.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(59, 29)` counted closure**: period `29`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 13` (and window `K >= 22`). -/
theorem towerME_ineq_59_29 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 59) (hK : (class1SlopeDatum ctx).K₀ = 29)
    (hm : towerSparsityBlock ctx ≤ 13) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_59_29.1 towerME_cyc_59_29.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(61, 30)` counted closure**: period `30`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 13` (and window `K >= 22`). -/
theorem towerME_ineq_61_30 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 61) (hK : (class1SlopeDatum ctx).K₀ = 30)
    (hm : towerSparsityBlock ctx ≤ 13) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_61_30.1 towerME_cyc_61_30.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(67, 33)` counted closure**: period `33`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 14` (and window `K >= 22`). -/
theorem towerME_ineq_67_33 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 67) (hK : (class1SlopeDatum ctx).K₀ = 33)
    (hm : towerSparsityBlock ctx ≤ 14) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_67_33.1 towerME_cyc_67_33.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(69, 11)` counted closure**: period `11`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 4` (and window `K >= 22`). -/
theorem towerME_ineq_69_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 11)
    (hm : towerSparsityBlock ctx ≤ 4) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_69_11.1 towerME_cyc_69_11.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(69, 34)` counted closure**: period `11`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 4` (and window `K >= 22`). -/
theorem towerME_ineq_69_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 34)
    (hm : towerSparsityBlock ctx ≤ 4) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_69_34.1 towerME_cyc_69_34.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(71, 35)` counted closure**: period `21`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 20` (and window `K >= 22`). -/
theorem towerME_ineq_71_35 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 71) (hK : (class1SlopeDatum ctx).K₀ = 35)
    (hm : towerSparsityBlock ctx ≤ 20) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_71_35.1 towerME_cyc_71_35.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(73, 36)` counted closure**: period `6`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 5` (and window `K >= 22`). -/
theorem towerME_ineq_73_36 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 73) (hK : (class1SlopeDatum ctx).K₀ = 36)
    (hm : towerSparsityBlock ctx ≤ 5) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_73_36.1 towerME_cyc_73_36.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(75, 7)` counted closure**: period `11`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 10` (and window `K >= 22`). -/
theorem towerME_ineq_75_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hm : towerSparsityBlock ctx ≤ 10) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_75_7.1 towerME_cyc_75_7.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(75, 12)` counted closure**: period `10`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 9` (and window `K >= 22`). -/
theorem towerME_ineq_75_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hm : towerSparsityBlock ctx ≤ 9) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_75_12.1 towerME_cyc_75_12.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(75, 37)` counted closure**: period `11`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 10` (and window `K >= 22`). -/
theorem towerME_ineq_75_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 37)
    (hm : towerSparsityBlock ctx ≤ 10) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_75_37.1 towerME_cyc_75_37.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(77, 3)` counted closure**: period `15`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 14` (and window `K >= 22`). -/
theorem towerME_ineq_77_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 77) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hm : towerSparsityBlock ctx ≤ 14) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_77_3.1 towerME_cyc_77_3.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(77, 5)` counted closure**: period `15`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 14` (and window `K >= 22`). -/
theorem towerME_ineq_77_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 77) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hm : towerSparsityBlock ctx ≤ 14) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_77_5.1 towerME_cyc_77_5.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(77, 38)` counted closure**: period `15`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 14` (and window `K >= 22`). -/
theorem towerME_ineq_77_38 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 77) (hK : (class1SlopeDatum ctx).K₀ = 38)
    (hm : towerSparsityBlock ctx ≤ 14) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_77_38.1 towerME_cyc_77_38.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(79, 39)` counted closure**: period `22`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 20` (and window `K >= 22`). -/
theorem towerME_ineq_79_39 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 79) (hK : (class1SlopeDatum ctx).K₀ = 39)
    (hm : towerSparsityBlock ctx ≤ 20) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_79_39.1 towerME_cyc_79_39.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(81, 1)` counted closure**: period `27`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 25` (and window `K >= 22`). -/
theorem towerME_ineq_81_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 81) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hm : towerSparsityBlock ctx ≤ 25) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_81_1.1 towerME_cyc_81_1.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(81, 4)` counted closure**: period `27`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 25` (and window `K >= 22`). -/
theorem towerME_ineq_81_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 81) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (hm : towerSparsityBlock ctx ≤ 25) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_81_4.1 towerME_cyc_81_4.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(81, 13)` counted closure**: period `27`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 25` (and window `K >= 22`). -/
theorem towerME_ineq_81_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 81) (hK : (class1SlopeDatum ctx).K₀ = 13)
    (hm : towerSparsityBlock ctx ≤ 25) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_81_13.1 towerME_cyc_81_13.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(81, 40)` counted closure**: period `27`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 25` (and window `K >= 22`). -/
theorem towerME_ineq_81_40 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 81) (hK : (class1SlopeDatum ctx).K₀ = 40)
    (hm : towerSparsityBlock ctx ≤ 25) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_81_40.1 towerME_cyc_81_40.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(83, 41)` counted closure**: period `41`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 18` (and window `K >= 22`). -/
theorem towerME_ineq_83_41 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 83) (hK : (class1SlopeDatum ctx).K₀ = 41)
    (hm : towerSparsityBlock ctx ≤ 18) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_83_41.1 towerME_cyc_83_41.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(87, 1)` counted closure**: period `11`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 10` (and window `K >= 22`). -/
theorem towerME_ineq_87_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hm : towerSparsityBlock ctx ≤ 10) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_87_1.1 towerME_cyc_87_1.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(87, 14)` counted closure**: period `11`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 10` (and window `K >= 22`). -/
theorem towerME_ineq_87_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hm : towerSparsityBlock ctx ≤ 10) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_87_14.1 towerME_cyc_87_14.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(89, 44)` counted closure**: period `7`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 6` (and window `K >= 22`). -/
theorem towerME_ineq_89_44 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 89) (hK : (class1SlopeDatum ctx).K₀ = 44)
    (hm : towerSparsityBlock ctx ≤ 6) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_89_44.1 towerME_cyc_89_44.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(95, 2)` counted closure**: period `14`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 6` (and window `K >= 22`). -/
theorem towerME_ineq_95_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 95) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hm : towerSparsityBlock ctx ≤ 6) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_95_2.1 towerME_cyc_95_2.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(95, 9)` counted closure**: period `14`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 6` (and window `K >= 22`). -/
theorem towerME_ineq_95_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 95) (hK : (class1SlopeDatum ctx).K₀ = 9)
    (hm : towerSparsityBlock ctx ≤ 6) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_95_9.1 towerME_cyc_95_9.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(95, 47)` counted closure**: period `22`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 20` (and window `K >= 22`). -/
theorem towerME_ineq_95_47 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 95) (hK : (class1SlopeDatum ctx).K₀ = 47)
    (hm : towerSparsityBlock ctx ≤ 20) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_95_47.1 towerME_cyc_95_47.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(97, 48)` counted closure**: period `24`, band-4 count `2` - the cycle
inequality holds on every shell with `m0 <= 10` (and window `K >= 22`). -/
theorem towerME_ineq_97_48 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 97) (hK : (class1SlopeDatum ctx).K₀ = 48)
    (hm : towerSparsityBlock ctx ≤ 10) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_97_48.1 towerME_cyc_97_48.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(99, 5)` counted closure**: period `15`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 14` (and window `K >= 22`). -/
theorem towerME_ineq_99_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hm : towerSparsityBlock ctx ≤ 14) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_99_5.1 towerME_cyc_99_5.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(101, 50)` counted closure**: period `50`, band-4 count `3` - the cycle
inequality holds on every shell with `m0 <= 14` (and window `K >= 22`). -/
theorem towerME_ineq_101_50 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 101) (hK : (class1SlopeDatum ctx).K₀ = 50)
    (hm : towerSparsityBlock ctx ≤ 14) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_101_50.1 towerME_cyc_101_50.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-- **The `(103, 51)` counted closure**: period `28`, band-4 count `1` - the cycle
inequality holds on every shell with `m0 <= 26` (and window `K >= 22`). -/
theorem towerME_ineq_103_51 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 103) (hK : (class1SlopeDatum ctx).K₀ = 51)
    (hm : towerSparsityBlock ctx ≤ 26) (hK22 : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_count ctx hq hK (by norm_num)
    towerME_cyc_103_51.1 towerME_cyc_103_51.2
    (towerME_numeric ctx (by norm_num) hm hK22 (by norm_num) (by decide))

/-! ## Part 7.  The high-band-4-density hard pair `(63, 10)` - recorded exactly -/

/-- **The hard pair `(63, 10)`** (pin divisor `21 | 63`): the recurrent cycle is
`17 -> 5` (period `2`) with canonical gaps `2, 4` - band-4 density `1/2`.  The demanded
density `1/m0` is `<= 1/2` on EVERY deep shell (`m0 >= 2`), so cycle counting closes
nothing here: `(63, 10)` joins `(15, 1), (15, 2), (105, 7)` in the hard core. -/
theorem towerME_hard_63_10 :
    slopeOrbit 63 10 (1 + 2) = slopeOrbit 63 10 1
      ∧ canonGap 63 (slopeOrbit 63 10 1) = 2
      ∧ canonGap 63 (slopeOrbit 63 10 2) = 4 := by
  have e0 : slopeOrbit 63 10 0 = 10 := rfl
  have e1 : slopeOrbit 63 10 1 = 17 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 10 2 = 5 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 10 3 = 17 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · show slopeOrbit 63 10 3 = slopeOrbit 63 10 1
    rw [e3, e1]
  · rw [e1]
    exact canonGap_eval (g := 1) (by norm_num) (by norm_num) (by norm_num)
  · rw [e2]
    exact canonGap_eval (g := 3) (by norm_num) (by norm_num) (by norm_num)

/-! ## Part 8.  The successor escape surface and the strictly smaller residual -/

/-- The enumerated escape triples `(q, K0, t)`: the cycle inequality is still demanded
on the datum `(q, K0)` exactly when `t <= m0`.  Counted pairs carry `t = threshold + 1`;
the hard pair `(63, 10)` carries `t = 2` (every deep shell). -/
def towerEnumHardTriples : List (ℕ × ℕ × ℕ) :=
  [(25, 2, 10), (25, 12, 10), (29, 14, 14), (35, 3, 7), (35, 17, 7), (37, 18, 18), (39, 6, 6), 
   (41, 20, 10), (47, 23, 14), (49, 3, 11), (49, 24, 11), (53, 26, 25), (55, 5, 5), (57, 1, 9), 
   (57, 28, 9), (59, 29, 14), (61, 30, 14), (63, 10, 2), (67, 33, 15), (69, 11, 5), 
   (69, 34, 5), (71, 35, 21), (73, 36, 6), (75, 7, 11), (75, 12, 10), (75, 37, 11), 
   (77, 3, 15), (77, 5, 15), (77, 38, 15), (79, 39, 21), (81, 1, 26), (81, 4, 26), 
   (81, 13, 26), (81, 40, 26), (83, 41, 19), (87, 1, 11), (87, 14, 11), (89, 44, 7), 
   (95, 2, 7), (95, 9, 7), (95, 47, 21), (97, 48, 11), (99, 5, 15), (101, 50, 15), 
   (103, 51, 27)]

/-- Every enumerated escape triple sits in the enumerated window `25 <= q <= 103`. -/
theorem towerEnumHardTriples_window :
    ∀ p ∈ towerEnumHardTriples, 25 ≤ p.1 ∧ p.1 ≤ 103 := by decide

/-- The enumerated part of the successor escape surface: some listed triple matches the
actual datum and the sparsity block has reached its escape threshold. -/
def TowerEnumEscape (ctx : ActualFailureContext) : Prop :=
  ∃ p ∈ towerEnumHardTriples,
    (class1SlopeDatum ctx).q = p.1 ∧ (class1SlopeDatum ctx).K₀ = p.2.1
      ∧ p.2.2 ≤ towerSparsityBlock ctx

/-- **The wave-5 escape surface**: the wave-4 counted families and fixed pairs, the
enumerated `25 <= q <= 103` data ABOVE their per-pair thresholds (band-4-free data are
gone entirely), and the un-enumerated odd moduli `107 <= q`. -/
def TowerModulusEnumEscape (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 9 ∧ 3 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 11 ∧ 5 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 13 ∧ 6 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 105
      ∧ ((class1SlopeDatum ctx).K₀ = 7 ∨ 8 ≤ towerSparsityBlock ctx))
  ∨ TowerEnumEscape ctx
  ∨ 107 ≤ (class1SlopeDatum ctx).q

/-- **The wave-5 Tower residual**: the cycle inequality demanded ONLY on deep shells
whose datum escapes every closure up to and including this module - strictly smaller
than the wave-4 `TowerFixedPointResidual` (witness below). -/
def TowerModulusEnumerationResidual : Prop :=
  ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
    TowerModulusEnumEscape ctx → Class2CycleInequality ctx

/-- The wave-4 residual discharges the wave-5 residual (weakening witness: the new
surface is contained in the old one). -/
theorem towerModulusEnumerationResidual_of_fixedPointResidual
    (h : TowerFixedPointResidual) : TowerModulusEnumerationResidual := by
  intro ctx hdeep hesc
  refine h ctx hdeep ?_
  rcases hesc with he | he | he | he | he | he | he
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
  · obtain ⟨p, hp, hq, -, -⟩ := he
    obtain ⟨h1, h2⟩ := towerEnumHardTriples_window p hp
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

/-- **The wave-4 residual from the wave-5 residual** - the enumeration dispatcher: on the
escape surface of `TowerFixedPointResidual` the un-enumerated disjunct `25 <= q != 105`
is split over the forty pinned moduli; band-4-free data close by fibre emptiness,
counted data close below their thresholds, and everything else lands in the strictly
smaller wave-5 surface. -/
theorem towerFixedPointResidual_of_modulusEnumeration
    (hres : TowerModulusEnumerationResidual) : TowerFixedPointResidual := by
  intro ctx hdeep hesc
  have hodd : (class1SlopeDatum ctx).q % 2 = 1 :=
    Nat.odd_iff.mp (class1SlopeDatum ctx).hq_odd
  have hr21 := r_ge_21_of_deep ctx hdeep
  have hKr := r_add_one_le_width ctx
  have hK22 : 22 ≤ shellWidth ctx := by omega
  have hdefm : towerSparsityBlock ctx = (3 * (ctx.n24CarryData.r + 1) + 63) / 64 := rfl
  have hm2 : 2 ≤ towerSparsityBlock ctx := by omega
  rcases hesc with he | he | he | he | he | he
  · exact hres ctx hdeep (Or.inl he)
  · exact hres ctx hdeep (Or.inr (Or.inl he))
  · exact hres ctx hdeep (Or.inr (Or.inr (Or.inl he)))
  · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inl he))))
  · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
  · obtain ⟨h25, h105⟩ := he
    rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 105 with hlt | hge
    · have hq40 : (class1SlopeDatum ctx).q = 25
          ∨ (class1SlopeDatum ctx).q = 27
          ∨ (class1SlopeDatum ctx).q = 29
          ∨ (class1SlopeDatum ctx).q = 31
          ∨ (class1SlopeDatum ctx).q = 33
          ∨ (class1SlopeDatum ctx).q = 35
          ∨ (class1SlopeDatum ctx).q = 37
          ∨ (class1SlopeDatum ctx).q = 39
          ∨ (class1SlopeDatum ctx).q = 41
          ∨ (class1SlopeDatum ctx).q = 43
          ∨ (class1SlopeDatum ctx).q = 45
          ∨ (class1SlopeDatum ctx).q = 47
          ∨ (class1SlopeDatum ctx).q = 49
          ∨ (class1SlopeDatum ctx).q = 51
          ∨ (class1SlopeDatum ctx).q = 53
          ∨ (class1SlopeDatum ctx).q = 55
          ∨ (class1SlopeDatum ctx).q = 57
          ∨ (class1SlopeDatum ctx).q = 59
          ∨ (class1SlopeDatum ctx).q = 61
          ∨ (class1SlopeDatum ctx).q = 63
          ∨ (class1SlopeDatum ctx).q = 65
          ∨ (class1SlopeDatum ctx).q = 67
          ∨ (class1SlopeDatum ctx).q = 69
          ∨ (class1SlopeDatum ctx).q = 71
          ∨ (class1SlopeDatum ctx).q = 73
          ∨ (class1SlopeDatum ctx).q = 75
          ∨ (class1SlopeDatum ctx).q = 77
          ∨ (class1SlopeDatum ctx).q = 79
          ∨ (class1SlopeDatum ctx).q = 81
          ∨ (class1SlopeDatum ctx).q = 83
          ∨ (class1SlopeDatum ctx).q = 85
          ∨ (class1SlopeDatum ctx).q = 87
          ∨ (class1SlopeDatum ctx).q = 89
          ∨ (class1SlopeDatum ctx).q = 91
          ∨ (class1SlopeDatum ctx).q = 93
          ∨ (class1SlopeDatum ctx).q = 95
          ∨ (class1SlopeDatum ctx).q = 97
          ∨ (class1SlopeDatum ctx).q = 99
          ∨ (class1SlopeDatum ctx).q = 101
          ∨ (class1SlopeDatum ctx).q = 103
          := by omega
      rcases hq40 with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
      · -- q = 25
        rcases towerME_pin_25 ctx hq with hv | hv
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 10 with hm | hm
          · exact towerME_ineq_25_2 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(25, 2, 10), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 10 with hm | hm
          · exact towerME_ineq_25_12 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(25, 12, 10), by decide, hq, hv, hm⟩))))))
      · -- q = 27
        rcases towerME_pin_27 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_27_1.1 towerME_cyc_27_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_27_4.1 towerME_cyc_27_4.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_27_13.1 towerME_cyc_27_13.2
      · -- q = 29
        have hv := towerME_pin_29 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 14 with hm | hm
        · exact towerME_ineq_29_14 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(29, 14, 14), by decide, hq, hv, hm⟩))))))
      · -- q = 31
        have hv := towerME_pin_31 ctx hq
        exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
          towerME_cyc_31_15.1 towerME_cyc_31_15.2
      · -- q = 33
        rcases towerME_pin_33 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_33_1.1 towerME_cyc_33_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_33_5.1 towerME_cyc_33_5.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_33_16.1 towerME_cyc_33_16.2
      · -- q = 35
        rcases towerME_pin_35 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_35_2.1 towerME_cyc_35_2.2
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 7 with hm | hm
          · exact towerME_ineq_35_3 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(35, 3, 7), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 7 with hm | hm
          · exact towerME_ineq_35_17 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(35, 17, 7), by decide, hq, hv, hm⟩))))))
      · -- q = 37
        have hv := towerME_pin_37 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 18 with hm | hm
        · exact towerME_ineq_37_18 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(37, 18, 18), by decide, hq, hv, hm⟩))))))
      · -- q = 39
        rcases towerME_pin_39 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_39_1.1 towerME_cyc_39_1.2
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 6 with hm | hm
          · exact towerME_ineq_39_6 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(39, 6, 6), by decide, hq, hv, hm⟩))))))
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_39_19.1 towerME_cyc_39_19.2
      · -- q = 41
        have hv := towerME_pin_41 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 10 with hm | hm
        · exact towerME_ineq_41_20 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(41, 20, 10), by decide, hq, hv, hm⟩))))))
      · -- q = 43
        have hv := towerME_pin_43 ctx hq
        exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
          towerME_cyc_43_21.1 towerME_cyc_43_21.2
      · -- q = 45
        rcases towerME_pin_45 ctx hq with hv | hv | hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_45_1.1 towerME_cyc_45_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_45_2.1 towerME_cyc_45_2.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_45_4.1 towerME_cyc_45_4.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_45_7.1 towerME_cyc_45_7.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_45_22.1 towerME_cyc_45_22.2
      · -- q = 47
        have hv := towerME_pin_47 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 14 with hm | hm
        · exact towerME_ineq_47_23 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(47, 23, 14), by decide, hq, hv, hm⟩))))))
      · -- q = 49
        rcases towerME_pin_49 ctx hq with hv | hv
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 11 with hm | hm
          · exact towerME_ineq_49_3 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(49, 3, 11), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 11 with hm | hm
          · exact towerME_ineq_49_24 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(49, 24, 11), by decide, hq, hv, hm⟩))))))
      · -- q = 51
        rcases towerME_pin_51 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_51_1.1 towerME_cyc_51_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_51_8.1 towerME_cyc_51_8.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_51_25.1 towerME_cyc_51_25.2
      · -- q = 53
        have hv := towerME_pin_53 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 25 with hm | hm
        · exact towerME_ineq_53_26 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(53, 26, 25), by decide, hq, hv, hm⟩))))))
      · -- q = 55
        rcases towerME_pin_55 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_55_2.1 towerME_cyc_55_2.2
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 5 with hm | hm
          · exact towerME_ineq_55_5 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(55, 5, 5), by decide, hq, hv, hm⟩))))))
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_55_27.1 towerME_cyc_55_27.2
      · -- q = 57
        rcases towerME_pin_57 ctx hq with hv | hv | hv
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 9 with hm | hm
          · exact towerME_ineq_57_1 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(57, 1, 9), by decide, hq, hv, hm⟩))))))
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_57_9.1 towerME_cyc_57_9.2
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 9 with hm | hm
          · exact towerME_ineq_57_28 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(57, 28, 9), by decide, hq, hv, hm⟩))))))
      · -- q = 59
        have hv := towerME_pin_59 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 14 with hm | hm
        · exact towerME_ineq_59_29 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(59, 29, 14), by decide, hq, hv, hm⟩))))))
      · -- q = 61
        have hv := towerME_pin_61 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 14 with hm | hm
        · exact towerME_ineq_61_30 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(61, 30, 14), by decide, hq, hv, hm⟩))))))
      · -- q = 63
        rcases towerME_pin_63 ctx hq with hv | hv | hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_63_1.1 towerME_cyc_63_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_63_3.1 towerME_cyc_63_3.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_63_4.1 towerME_cyc_63_4.2
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(63, 10, 2), by decide, hq, hv, hm2⟩))))))
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_63_31.1 towerME_cyc_63_31.2
      · -- q = 65
        rcases towerME_pin_65 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_65_2.1 towerME_cyc_65_2.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_65_6.1 towerME_cyc_65_6.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_65_32.1 towerME_cyc_65_32.2
      · -- q = 67
        have hv := towerME_pin_67 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 15 with hm | hm
        · exact towerME_ineq_67_33 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(67, 33, 15), by decide, hq, hv, hm⟩))))))
      · -- q = 69
        rcases towerME_pin_69 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_69_1.1 towerME_cyc_69_1.2
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 5 with hm | hm
          · exact towerME_ineq_69_11 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(69, 11, 5), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 5 with hm | hm
          · exact towerME_ineq_69_34 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(69, 34, 5), by decide, hq, hv, hm⟩))))))
      · -- q = 71
        have hv := towerME_pin_71 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 21 with hm | hm
        · exact towerME_ineq_71_35 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(71, 35, 21), by decide, hq, hv, hm⟩))))))
      · -- q = 73
        have hv := towerME_pin_73 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 6 with hm | hm
        · exact towerME_ineq_73_36 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(73, 36, 6), by decide, hq, hv, hm⟩))))))
      · -- q = 75
        rcases towerME_pin_75 ctx hq with hv | hv | hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_75_1.1 towerME_cyc_75_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_75_2.1 towerME_cyc_75_2.2
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 11 with hm | hm
          · exact towerME_ineq_75_7 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(75, 7, 11), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 10 with hm | hm
          · exact towerME_ineq_75_12 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(75, 12, 10), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 11 with hm | hm
          · exact towerME_ineq_75_37 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(75, 37, 11), by decide, hq, hv, hm⟩))))))
      · -- q = 77
        rcases towerME_pin_77 ctx hq with hv | hv | hv
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 15 with hm | hm
          · exact towerME_ineq_77_3 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(77, 3, 15), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 15 with hm | hm
          · exact towerME_ineq_77_5 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(77, 5, 15), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 15 with hm | hm
          · exact towerME_ineq_77_38 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(77, 38, 15), by decide, hq, hv, hm⟩))))))
      · -- q = 79
        have hv := towerME_pin_79 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 21 with hm | hm
        · exact towerME_ineq_79_39 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(79, 39, 21), by decide, hq, hv, hm⟩))))))
      · -- q = 81
        rcases towerME_pin_81 ctx hq with hv | hv | hv | hv
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 26 with hm | hm
          · exact towerME_ineq_81_1 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(81, 1, 26), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 26 with hm | hm
          · exact towerME_ineq_81_4 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(81, 4, 26), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 26 with hm | hm
          · exact towerME_ineq_81_13 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(81, 13, 26), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 26 with hm | hm
          · exact towerME_ineq_81_40 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(81, 40, 26), by decide, hq, hv, hm⟩))))))
      · -- q = 83
        have hv := towerME_pin_83 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 19 with hm | hm
        · exact towerME_ineq_83_41 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(83, 41, 19), by decide, hq, hv, hm⟩))))))
      · -- q = 85
        rcases towerME_pin_85 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_85_2.1 towerME_cyc_85_2.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_85_8.1 towerME_cyc_85_8.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_85_42.1 towerME_cyc_85_42.2
      · -- q = 87
        rcases towerME_pin_87 ctx hq with hv | hv | hv
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 11 with hm | hm
          · exact towerME_ineq_87_1 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(87, 1, 11), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 11 with hm | hm
          · exact towerME_ineq_87_14 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(87, 14, 11), by decide, hq, hv, hm⟩))))))
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_87_43.1 towerME_cyc_87_43.2
      · -- q = 89
        have hv := towerME_pin_89 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 7 with hm | hm
        · exact towerME_ineq_89_44 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(89, 44, 7), by decide, hq, hv, hm⟩))))))
      · -- q = 91
        rcases towerME_pin_91 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_91_3.1 towerME_cyc_91_3.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_91_6.1 towerME_cyc_91_6.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_91_45.1 towerME_cyc_91_45.2
      · -- q = 93
        rcases towerME_pin_93 ctx hq with hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_93_1.1 towerME_cyc_93_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_93_15.1 towerME_cyc_93_15.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_93_46.1 towerME_cyc_93_46.2
      · -- q = 95
        rcases towerME_pin_95 ctx hq with hv | hv | hv
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 7 with hm | hm
          · exact towerME_ineq_95_2 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(95, 2, 7), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 7 with hm | hm
          · exact towerME_ineq_95_9 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(95, 9, 7), by decide, hq, hv, hm⟩))))))
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 21 with hm | hm
          · exact towerME_ineq_95_47 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(95, 47, 21), by decide, hq, hv, hm⟩))))))
      · -- q = 97
        have hv := towerME_pin_97 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 11 with hm | hm
        · exact towerME_ineq_97_48 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(97, 48, 11), by decide, hq, hv, hm⟩))))))
      · -- q = 99
        rcases towerME_pin_99 ctx hq with hv | hv | hv | hv | hv
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_99_1.1 towerME_cyc_99_1.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_99_4.1 towerME_cyc_99_4.2
        · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 15 with hm | hm
          · exact towerME_ineq_99_5 ctx hq hv (by omega) hK22
          · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(99, 5, 15), by decide, hq, hv, hm⟩))))))
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_99_16.1 towerME_cyc_99_16.2
        · exact class2CycleInequality_of_collision_free ctx hq hv (by norm_num)
            towerME_cyc_99_49.1 towerME_cyc_99_49.2
      · -- q = 101
        have hv := towerME_pin_101 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 15 with hm | hm
        · exact towerME_ineq_101_50 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(101, 50, 15), by decide, hq, hv, hm⟩))))))
      · -- q = 103
        have hv := towerME_pin_103 ctx hq
        rcases Nat.lt_or_ge (towerSparsityBlock ctx) 27 with hm | hm
        · exact towerME_ineq_103_51 ctx hq hv (by omega) hK22
        · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(103, 51, 27), by decide, hq, hv, hm⟩))))))
    · have h107 : 107 ≤ (class1SlopeDatum ctx).q := by omega
      exact hres ctx hdeep
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h107))))))

/-! ## Part 9.  The exact capstone bridges (additive only) -/

/-- **The exact capstone bridge**: the wave-5 residual rebuilds VERBATIM the `towerSplit`
field of `Erdos260CycleResidual`, through the wave-4 bridge
`towerSplit_of_fixedPointResidual` (the surface consumed by `Erdos260DatumCapstone`). -/
theorem towerSplit_of_modulusEnumeration (h : TowerModulusEnumerationResidual) :
    ∀ ctx : ActualFailureContext,
      towerShallowDepthBound < shellLadderDepth ctx →
      (class1SlopeDatum ctx).q < 9
      ∨ (16 < (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q < 25)
      ∨ Class2CycleInequality ctx :=
  towerSplit_of_fixedPointResidual (towerFixedPointResidual_of_modulusEnumeration h)

/-- **The full capstone count bound from the wave-5 residual**: `Class2DeepShellCountBound`
(the `towerCount` field of `Erdos260SharpResidual`) outright. -/
theorem towerCountBound_of_modulusEnumeration (h : TowerModulusEnumerationResidual) :
    Class2DeepShellCountBound :=
  towerCountBound_of_fixedPointResidual (towerFixedPointResidual_of_modulusEnumeration h)

/-! ## Part 10.  Honest machine-readable status -/

/-- The precise status of the Tower / Class 2 modulus enumeration after this module. -/
def towerModulusEnumerationStatus : List String :=
  [ "CLOSED (forty pin enumerations, NEW): every odd modulus 25 <= q <= 103 carries " ++
      "its exact divisor-pin K0 list (towerME_pin_25 .. towerME_pin_103, kernel decide " ++
      "over 2*K0+1 | q; the upper bound is Nat.le_of_dvd).  Together with the wave-3/4 " ++
      "closures of q < 9, q in {9,11,13,15}, 16 < q < 25 and q = 105, every modulus " ++
      "of the class-2 window below 107 is now enumerated.",
    "CLOSED (46 band-4-free data, unconditional fibre emptiness): " ++
      "(27,1) (27,4) (27,13) (31,15) (33,1) (33,5) (33,16) (35,2) (39,1) (39,19) " ++
      "(43,21) (45,1) (45,2) (45,4) (45,7) (45,22) (51,1) (51,8) (51,25) (55,2) " ++
      "(55,27) (57,9) (63,1) (63,3) (63,4) (63,31) (65,2) (65,6) (65,32) (69,1) " ++
      "(75,1) (75,2) (85,2) (85,8) (85,42) (87,43) (91,3) (91,6) (91,45) (93,1) " ++
      "(93,15) (93,46) (99,1) (99,4) (99,16) (99,49)" ++
      " (towerME_empty_*, via class2Fibre_empty_of_collision_free; each also yields " ++
      "the cycle inequality at EVERY sparsity block).",
    "CLOSED (10 whole moduli, NEW headline): q in {27, 31, 33, 43, 45, 51, 65, 85, 91, 93} " ++
      "have EVERY pin-admissible K0 on a band-4-free cycle - the class-2 routed fibre " ++
      "is empty on every such shell (towerME_empty_mod_*), no residual demand at all.",
    "CLOSED (44 counted data up to explicit thresholds): the cycle meets band 4 " ++
      "(b4 >= 1 per period c) and the cycle inequality m0*(b4*ceil(K/c)) <= K closes " ++
      "for every m0 <= t via the reusable splitter towerME_numeric (width floor " ++
      "towerMEWidth/towerMEWidth_le from the order pin 64*m0 <= 3(r+1)+63, kernel " ++
      "per-level checks).  Thresholds: " ++
      "(25,2): c=10, b4=1, m0<=9; (25,12): c=10, b4=1, m0<=9; (29,14): c=14, b4=1, m0<=13; " ++
      "(35,3): c=7, b4=1, m0<=6; (35,17): c=7, b4=1, m0<=6; (37,18): c=18, b4=1, m0<=17; " ++
      "(39,6): c=6, b4=1, m0<=5; (41,20): c=10, b4=1, m0<=9; (47,23): c=14, b4=1, m0<=13; " ++
      "(49,3): c=11, b4=1, m0<=10; (49,24): c=11, b4=1, m0<=10; (53,26): c=26, b4=1, m0<=24; " ++
      "(55,5): c=5, b4=1, m0<=4; (57,1): c=9, b4=1, m0<=8; (57,28): c=9, b4=1, m0<=8; " ++
      "(59,29): c=29, b4=2, m0<=13; (61,30): c=30, b4=2, m0<=13; (67,33): c=33, b4=2, m0<=14; " ++
      "(69,11): c=11, b4=2, m0<=4; (69,34): c=11, b4=2, m0<=4; (71,35): c=21, b4=1, m0<=20; " ++
      "(73,36): c=6, b4=1, m0<=5; (75,7): c=11, b4=1, m0<=10; (75,12): c=10, b4=1, m0<=9; " ++
      "(75,37): c=11, b4=1, m0<=10; (77,3): c=15, b4=1, m0<=14; (77,5): c=15, b4=1, m0<=14; " ++
      "(77,38): c=15, b4=1, m0<=14; (79,39): c=22, b4=1, m0<=20; (81,1): c=27, b4=1, m0<=25; " ++
      "(81,4): c=27, b4=1, m0<=25; (81,13): c=27, b4=1, m0<=25; (81,40): c=27, b4=1, m0<=25; " ++
      "(83,41): c=41, b4=2, m0<=18; (87,1): c=11, b4=1, m0<=10; (87,14): c=11, b4=1, m0<=10; " ++
      "(89,44): c=7, b4=1, m0<=6; (95,2): c=14, b4=2, m0<=6; (95,9): c=14, b4=2, m0<=6; " ++
      "(95,47): c=22, b4=1, m0<=20; (97,48): c=24, b4=2, m0<=10; (99,5): c=15, b4=1, m0<=14; " ++
      "(101,50): c=50, b4=3, m0<=14; (103,51): c=28, b4=1, m0<=26;",
    "RECORDED (the high-band-4-density hard core, NEW): (63, 10) rides the period-2 " ++
      "cycle 17 -> 5 with gaps 2, 4 (towerME_hard_63_10) - band-4 density 1/2, so the " ++
      "demanded density 1/m0 <= 1/2 on EVERY deep shell (m0 >= 2) and cycle counting " ++
      "closes nothing; (63, 10) joins the fixed pairs (15,1), (15,2), (105,7) as the " ++
      "hard core (its datum pins oddpart(Q) = 3 via 63 = oddpart(Q)*21).  All other " ++
      "densities among the 91 enumerated data are <= 2/11.",
    "REDUCED (the strictly smaller wave-5 residual + exact capstone bridge): " ++
      "TowerModulusEnumerationResidual demands the cycle inequality only on " ++
      "TowerModulusEnumEscape = the wave-4 families (q = 9 m0 >= 3; q = 11 m0 >= 5; " ++
      "q = 13 m0 >= 6; q = 15 K0 <= 2; q = 105 on K0 = 7 or m0 >= 8) plus the " ++
      "45 enumerated triples of towerEnumHardTriples (44 counted pairs above their " ++
      "thresholds + the hard pair (63,10) at every deep shell) plus the un-enumerated " ++
      "odd moduli 107 <= q.  towerFixedPointResidual_of_modulusEnumeration rebuilds " ++
      "the wave-4 residual; towerSplit_of_modulusEnumeration rebuilds the capstone " ++
      "towerSplit field VERBATIM; towerCountBound_of_modulusEnumeration discharges " ++
      "Class2DeepShellCountBound; towerModulusEnumerationResidual_of_fixedPointResidual " ++
      "witnesses the new residual is no stronger than the wave-4 one.",
    "HONESTLY NOT CLOSED: the three fixed pairs (15,1), (15,2), (105,7) (b4 = c); the " ++
      "hard pair (63,10) (b4/c = 1/2 >= 1/m0 on deep shells); the counted families " ++
      "above their per-pair thresholds (demanded density 1/m0 below cycle density " ++
      "b4/c); the wave-4 counted families q in {9,11,13} and (105,52) above theirs; " ++
      "and the un-enumerated odd moduli 107 <= q (the method extends mechanically). " ++
      "We do NOT claim unconditional closure of the towerSplit field.",
    "NON-DEGENERATE: every theorem is about the genuine class1SlopeDatum of the " ++
      "actual failing-shell context (q = oddpart(Q*(2|P|+1)), K0 = |P|) and the " ++
      "genuine routed class-2 fibre of genuineChargeRoute; orbit tables are explicit " ++
      "E.13 step evaluations (slopeOrbit_step_eval) against the canonical band bounds; " ++
      "pin scans and numeric level checks are kernel decide (NOT native_decide); " ++
      "emptiness results are proved impossibility theorems, not fabricated witnesses." ]

theorem towerModulusEnumerationStatus_nonempty :
    towerModulusEnumerationStatus ≠ [] := by
  simp [towerModulusEnumerationStatus]

/-! ## Part 11.  Axiom-cleanliness audit -/

#print axioms towerMEWidth_le
#print axioms towerME_numeric
#print axioms towerME_pin_25
#print axioms towerME_pin_27
#print axioms towerME_pin_29
#print axioms towerME_pin_31
#print axioms towerME_pin_33
#print axioms towerME_pin_35
#print axioms towerME_pin_37
#print axioms towerME_pin_39
#print axioms towerME_pin_41
#print axioms towerME_pin_43
#print axioms towerME_pin_45
#print axioms towerME_pin_47
#print axioms towerME_pin_49
#print axioms towerME_pin_51
#print axioms towerME_pin_53
#print axioms towerME_pin_55
#print axioms towerME_pin_57
#print axioms towerME_pin_59
#print axioms towerME_pin_61
#print axioms towerME_pin_63
#print axioms towerME_pin_65
#print axioms towerME_pin_67
#print axioms towerME_pin_69
#print axioms towerME_pin_71
#print axioms towerME_pin_73
#print axioms towerME_pin_75
#print axioms towerME_pin_77
#print axioms towerME_pin_79
#print axioms towerME_pin_81
#print axioms towerME_pin_83
#print axioms towerME_pin_85
#print axioms towerME_pin_87
#print axioms towerME_pin_89
#print axioms towerME_pin_91
#print axioms towerME_pin_93
#print axioms towerME_pin_95
#print axioms towerME_pin_97
#print axioms towerME_pin_99
#print axioms towerME_pin_101
#print axioms towerME_pin_103
#print axioms towerME_empty_27_1
#print axioms towerME_empty_27_4
#print axioms towerME_empty_27_13
#print axioms towerME_empty_31_15
#print axioms towerME_empty_33_1
#print axioms towerME_empty_33_5
#print axioms towerME_empty_33_16
#print axioms towerME_empty_35_2
#print axioms towerME_empty_39_1
#print axioms towerME_empty_39_19
#print axioms towerME_empty_43_21
#print axioms towerME_empty_45_1
#print axioms towerME_empty_45_2
#print axioms towerME_empty_45_4
#print axioms towerME_empty_45_7
#print axioms towerME_empty_45_22
#print axioms towerME_empty_51_1
#print axioms towerME_empty_51_8
#print axioms towerME_empty_51_25
#print axioms towerME_empty_55_2
#print axioms towerME_empty_55_27
#print axioms towerME_empty_57_9
#print axioms towerME_empty_63_1
#print axioms towerME_empty_63_3
#print axioms towerME_empty_63_4
#print axioms towerME_empty_63_31
#print axioms towerME_empty_65_2
#print axioms towerME_empty_65_6
#print axioms towerME_empty_65_32
#print axioms towerME_empty_69_1
#print axioms towerME_empty_75_1
#print axioms towerME_empty_75_2
#print axioms towerME_empty_85_2
#print axioms towerME_empty_85_8
#print axioms towerME_empty_85_42
#print axioms towerME_empty_87_43
#print axioms towerME_empty_91_3
#print axioms towerME_empty_91_6
#print axioms towerME_empty_91_45
#print axioms towerME_empty_93_1
#print axioms towerME_empty_93_15
#print axioms towerME_empty_93_46
#print axioms towerME_empty_99_1
#print axioms towerME_empty_99_4
#print axioms towerME_empty_99_16
#print axioms towerME_empty_99_49
#print axioms towerME_empty_mod_27
#print axioms towerME_empty_mod_31
#print axioms towerME_empty_mod_33
#print axioms towerME_empty_mod_43
#print axioms towerME_empty_mod_45
#print axioms towerME_empty_mod_51
#print axioms towerME_empty_mod_65
#print axioms towerME_empty_mod_85
#print axioms towerME_empty_mod_91
#print axioms towerME_empty_mod_93
#print axioms towerME_ineq_25_2
#print axioms towerME_ineq_25_12
#print axioms towerME_ineq_29_14
#print axioms towerME_ineq_35_3
#print axioms towerME_ineq_35_17
#print axioms towerME_ineq_37_18
#print axioms towerME_ineq_39_6
#print axioms towerME_ineq_41_20
#print axioms towerME_ineq_47_23
#print axioms towerME_ineq_49_3
#print axioms towerME_ineq_49_24
#print axioms towerME_ineq_53_26
#print axioms towerME_ineq_55_5
#print axioms towerME_ineq_57_1
#print axioms towerME_ineq_57_28
#print axioms towerME_ineq_59_29
#print axioms towerME_ineq_61_30
#print axioms towerME_ineq_67_33
#print axioms towerME_ineq_69_11
#print axioms towerME_ineq_69_34
#print axioms towerME_ineq_71_35
#print axioms towerME_ineq_73_36
#print axioms towerME_ineq_75_7
#print axioms towerME_ineq_75_12
#print axioms towerME_ineq_75_37
#print axioms towerME_ineq_77_3
#print axioms towerME_ineq_77_5
#print axioms towerME_ineq_77_38
#print axioms towerME_ineq_79_39
#print axioms towerME_ineq_81_1
#print axioms towerME_ineq_81_4
#print axioms towerME_ineq_81_13
#print axioms towerME_ineq_81_40
#print axioms towerME_ineq_83_41
#print axioms towerME_ineq_87_1
#print axioms towerME_ineq_87_14
#print axioms towerME_ineq_89_44
#print axioms towerME_ineq_95_2
#print axioms towerME_ineq_95_9
#print axioms towerME_ineq_95_47
#print axioms towerME_ineq_97_48
#print axioms towerME_ineq_99_5
#print axioms towerME_ineq_101_50
#print axioms towerME_ineq_103_51
#print axioms towerME_hard_63_10
#print axioms towerEnumHardTriples_window
#print axioms towerModulusEnumerationResidual_of_fixedPointResidual
#print axioms towerFixedPointResidual_of_modulusEnumeration
#print axioms towerSplit_of_modulusEnumeration
#print axioms towerCountBound_of_modulusEnumeration
#print axioms towerModulusEnumerationStatus_nonempty

end

end Erdos260
