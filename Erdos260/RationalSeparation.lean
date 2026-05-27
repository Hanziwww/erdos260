import Mathlib

/-!
# Rational separation

This file isolates the elementary denominator-separation estimate used in the
fixed-period repetition argument: two rationals with denominators `Q` and `B`
are either equal or separated by at least `1 / (Q * B)`.
-/

namespace Erdos260

noncomputable section

theorem one_le_abs_int_cast_of_ne_zero {z : Int} (hz : z ≠ 0) :
    (1 : ℝ) <= |(z : ℝ)| := by
  have hzabs : 1 <= z.natAbs := Int.natAbs_pos.mpr hz
  have hzreal : (1 : ℝ) <= (z.natAbs : ℝ) := by exact_mod_cast hzabs
  simpa [Nat.cast_natAbs] using hzreal

theorem rat_div_abs_sub_lower_bound_of_cross_ne_zero
    {P A : Int} {Q B : Nat} (hQ : 0 < Q) (hB : 0 < B)
    (hneq : P * (B : Int) - A * (Q : Int) ≠ 0) :
    (1 : ℝ) / ((Q : ℝ) * (B : ℝ)) <=
      |(P : ℝ) / (Q : ℝ) - (A : ℝ) / (B : ℝ)| := by
  let z : Int := P * (B : Int) - A * (Q : Int)
  have hzabs : (1 : ℝ) <= |(z : ℝ)| :=
    one_le_abs_int_cast_of_ne_zero hneq
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
  have hdenpos : 0 < (Q : ℝ) * (B : ℝ) := mul_pos hQpos hBpos
  have hdiff :
      (P : ℝ) / (Q : ℝ) - (A : ℝ) / (B : ℝ) =
        (z : ℝ) / ((Q : ℝ) * (B : ℝ)) := by
    have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
    have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
    dsimp [z]
    field_simp [hQne, hBne]
    norm_num [Nat.cast_mul, Int.cast_sub, Int.cast_mul]
    ring
  have hfrac :
      |(z : ℝ)| / ((Q : ℝ) * (B : ℝ)) =
        |(P : ℝ) / (Q : ℝ) - (A : ℝ) / (B : ℝ)| := by
    rw [hdiff]
    rw [abs_div, abs_of_pos hdenpos]
  calc
    (1 : ℝ) / ((Q : ℝ) * (B : ℝ)) <= |(z : ℝ)| / ((Q : ℝ) * (B : ℝ)) := by
      exact div_le_div_of_nonneg_right hzabs hdenpos.le
    _ = |(P : ℝ) / (Q : ℝ) - (A : ℝ) / (B : ℝ)| := hfrac

theorem rat_div_eq_of_abs_sub_lt_inv_mul
    {P A : Int} {Q B : Nat} (hQ : 0 < Q) (hB : 0 < B)
    (hlt :
      |(P : ℝ) / (Q : ℝ) - (A : ℝ) / (B : ℝ)| <
        (1 : ℝ) / ((Q : ℝ) * (B : ℝ))) :
    (P : ℝ) / (Q : ℝ) = (A : ℝ) / (B : ℝ) := by
  by_cases hnum : P * (B : Int) - A * (Q : Int) = 0
  · have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
    have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
    have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
    have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
    have hnumReal : (P : ℝ) * (B : ℝ) - (A : ℝ) * (Q : ℝ) = 0 := by
      exact_mod_cast hnum
    field_simp [hQne, hBne]
    nlinarith
  · have hlower :=
      rat_div_abs_sub_lower_bound_of_cross_ne_zero (P := P) (A := A)
        (Q := Q) (B := B) hQ hB hnum
    linarith

end

end Erdos260
