import Erdos260.PolynomialWindow.Polynomial
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Integral carries for polynomial weights

This file formalizes the exact carry recurrence before any window counting is
introduced.  The weight is an integral polynomial; positivity is required only
on the tail, which is the form produced by the normalization in
`Polynomial.lean`.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos260.PolynomialWindow

/-- The support digit, embedded directly in `ℤ`. -/
def supportDigitInt (S : Set ℕ) (n : ℕ) : ℤ := by
  classical
  exact if n ∈ S then 1 else 0

/-- A polynomial weight evaluated at a natural number. -/
def intPolynomialValue (w : Polynomial ℤ) (n : ℕ) : ℤ :=
  w.eval (n : ℤ)

/-- Sum of the absolute values of the coefficients, viewed in `ℝ`. -/
def polynomialCoefficientMass (w : Polynomial ℤ) : ℝ :=
  ∑ i ∈ Finset.range (w.natDegree + 1), |(w.coeff i : ℝ)|

theorem polynomialCoefficientMass_nonneg (w : Polynomial ℤ) :
    0 ≤ polynomialCoefficientMass w := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem polynomialCoefficientMass_pos {w : Polynomial ℤ} (hw : w ≠ 0) :
    0 < polynomialCoefficientMass w := by
  have hlead : w.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hw
  have hmem : w.natDegree ∈ Finset.range (w.natDegree + 1) := by simp
  have hterm : 0 < |(w.coeff w.natDegree : ℝ)| := by
    rw [Polynomial.coeff_natDegree, abs_pos]
    exact_mod_cast hlead
  unfold polynomialCoefficientMass
  exact hterm.trans_le
    (Finset.single_le_sum (fun i _ => abs_nonneg (w.coeff i : ℝ)) hmem)

/-- Global polynomial growth bound in a form suited to the geometric tail. -/
theorem abs_intPolynomialValue_le (w : Polynomial ℤ) (n : ℕ) :
    |(intPolynomialValue w n : ℝ)| ≤
      polynomialCoefficientMass w * (n + 1 : ℝ) ^ w.natDegree := by
  have heval :
      (intPolynomialValue w n : ℝ) =
        ∑ i ∈ Finset.range (w.natDegree + 1),
          (w.coeff i : ℝ) * (n : ℝ) ^ i := by
    unfold intPolynomialValue
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rfl
  rw [heval]
  calc
    |∑ i ∈ Finset.range (w.natDegree + 1),
        (w.coeff i : ℝ) * (n : ℝ) ^ i| ≤
        ∑ i ∈ Finset.range (w.natDegree + 1),
          |(w.coeff i : ℝ) * (n : ℝ) ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (w.natDegree + 1),
          |(w.coeff i : ℝ)| * (n + 1 : ℝ) ^ w.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hiDegree : i ≤ w.natDegree := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hn : (n : ℝ) ≤ n + 1 := by norm_num
      calc
        (n : ℝ) ^ i ≤ (n + 1 : ℝ) ^ i := by gcongr
        _ ≤ (n + 1 : ℝ) ^ w.natDegree := by
          exact pow_le_pow_right₀ (by norm_num) hiDegree
    _ = polynomialCoefficientMass w * (n + 1 : ℝ) ^ w.natDegree := by
      simp only [polynomialCoefficientMass, Finset.sum_mul]

/-- The fixed geometric moment controlling every shifted polynomial tail. -/
def geometricMoment (b d : ℕ) : ℝ :=
  ∑' j : ℕ, (j + 2 : ℝ) ^ d / (b : ℝ) ^ (j + 1)

theorem summable_geometricMoment_term {b d : ℕ} (hb : 2 ≤ b) :
    Summable fun j : ℕ => (j + 2 : ℝ) ^ d / (b : ℝ) ^ (j + 1) := by
  let r : ℝ := (b : ℝ)⁻¹
  have hbReal : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans hbReal)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (zero_lt_one.trans hbReal)),
      inv_lt_one₀ (zero_lt_one.trans hbReal)]
    exact hbReal
  have hbase : Summable fun n : ℕ => (n : ℝ) ^ d * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one d hr
  have hshift :
      Summable fun j : ℕ => (j + 2 : ℝ) ^ d * r ^ (j + 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ d * r ^ n) 2).mpr hbase
  have hscaled := hshift.mul_left (b : ℝ)
  have heq :
      (fun j : ℕ => (j + 2 : ℝ) ^ d / (b : ℝ) ^ (j + 1)) =
        fun j : ℕ => (b : ℝ) * ((j + 2 : ℝ) ^ d * r ^ (j + 2)) := by
    funext j
    dsimp [r]
    rw [div_eq_mul_inv, inv_pow, pow_succ]
    field_simp
    ring
  rw [heq]
  exact hscaled

theorem geometricMoment_nonneg {b d : ℕ} : 0 ≤ geometricMoment b d := by
  exact tsum_nonneg fun _ => by positivity

/-- Real summand associated with an integral polynomial weight. -/
def integralWeightedTerm (b : ℕ) (w : Polynomial ℤ)
    (S : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ S then
    (intPolynomialValue w n : ℝ) / (b : ℝ) ^ n
  else 0

theorem shifted_index_le_product (N j : ℕ) :
    N + j + 2 ≤ (N + 1) * (j + 2) := by
  nlinarith [Nat.zero_le N, Nat.zero_le j]

/-- Uniform pointwise majorant for the scaled shifted tail. -/
theorem scaled_integralWeightedTerm_abs_le {b : ℕ} (hb : 2 ≤ b)
    (w : Polynomial ℤ) (S : Set ℕ) (N j : ℕ) :
    (b : ℝ) ^ N *
        |integralWeightedTerm b w S (j + (N + 1))| ≤
      polynomialCoefficientMass w * (N + 1 : ℝ) ^ w.natDegree *
        ((j + 2 : ℝ) ^ w.natDegree / (b : ℝ) ^ (j + 1)) := by
  classical
  have hbpos : (0 : ℝ) < b := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hb)
  by_cases hj : j + (N + 1) ∈ S
  · rw [integralWeightedTerm, if_pos hj, abs_div,
      abs_of_pos (pow_pos hbpos _)]
    have hvalue := abs_intPolynomialValue_le w (j + (N + 1))
    have hindexNat : j + (N + 1) + 1 ≤ (N + 1) * (j + 2) := by
      nlinarith [Nat.zero_le N, Nat.zero_le j]
    have hindex :
        (j + (N + 1) + 1 : ℝ) ^ w.natDegree ≤
          ((N + 1 : ℝ) * (j + 2 : ℝ)) ^ w.natDegree := by
      gcongr
      exact_mod_cast hindexNat
    calc
      (b : ℝ) ^ N *
          (|(intPolynomialValue w (j + (N + 1)) : ℝ)| /
            (b : ℝ) ^ (j + (N + 1))) =
          (b : ℝ) ^ N *
            |(intPolynomialValue w (j + (N + 1)) : ℝ)| /
              (b : ℝ) ^ (j + (N + 1)) := by ring
      _ ≤
          (b : ℝ) ^ N *
            (polynomialCoefficientMass w *
              (j + (N + 1) + 1 : ℝ) ^ w.natDegree) /
                (b : ℝ) ^ (j + (N + 1)) := by
        gcongr
        simpa only [Nat.cast_add, Nat.cast_one] using hvalue
      _ ≤ (b : ℝ) ^ N *
            (polynomialCoefficientMass w *
              (((N + 1 : ℝ) * (j + 2 : ℝ)) ^ w.natDegree)) /
                (b : ℝ) ^ (j + (N + 1)) := by
        gcongr
        exact polynomialCoefficientMass_nonneg w
      _ = polynomialCoefficientMass w * (N + 1 : ℝ) ^ w.natDegree *
          ((j + 2 : ℝ) ^ w.natDegree / (b : ℝ) ^ (j + 1)) := by
        rw [mul_pow]
        have hpow :
            (b : ℝ) ^ (j + (N + 1)) =
              (b : ℝ) ^ N * (b : ℝ) ^ (j + 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hpow]
        field_simp
  · rw [integralWeightedTerm, if_neg hj, abs_zero, mul_zero]
    apply mul_nonneg
    · exact mul_nonneg (polynomialCoefficientMass_nonneg w) (by positivity)
    · exact div_nonneg (by positivity) (le_of_lt (pow_pos hbpos _))

/-- Data needed for the exact carry construction.  Eventual positivity is
kept as data because deleting the finitely many exceptional indices is part
of the public normalization bridge. -/
structure CarrySeries where
  base : ℕ
  base_ge_two : 2 ≤ base
  weight : Polynomial ℤ
  weight_ne_zero : weight ≠ 0
  support : Set ℕ
  support_infinite : support.Infinite
  value : ℚ
  hasSum : HasSum (integralWeightedTerm base weight support) (value : ℝ)
  positiveFrom : ℕ
  weight_pos : ∀ n, positiveFrom ≤ n → 0 < intPolynomialValue weight n

namespace CarrySeries

/-- Denominator of the rational value, as a positive integer. -/
def denominator (D : CarrySeries) : ℕ := D.value.den

theorem denominator_pos (D : CarrySeries) : 0 < D.denominator := by
  exact D.value.pos

/-- Finite-sum integer carry. -/
def carry (D : CarrySeries) (N : ℕ) : ℤ :=
  D.value.num * (D.base : ℤ) ^ N -
    (D.denominator : ℤ) *
      ∑ n ∈ Finset.Icc 0 N,
        intPolynomialValue D.weight n * supportDigitInt D.support n *
          (D.base : ℤ) ^ (N - n)

@[simp]
theorem supportDigitInt_of_mem (D : CarrySeries) {n : ℕ}
    (hn : n ∈ D.support) : supportDigitInt D.support n = 1 := by
  simp [supportDigitInt, hn]

@[simp]
theorem supportDigitInt_of_not_mem (D : CarrySeries) {n : ℕ}
    (hn : n ∉ D.support) : supportDigitInt D.support n = 0 := by
  simp [supportDigitInt, hn]

theorem integralWeightedTerm_eq (D : CarrySeries) (n : ℕ) :
    integralWeightedTerm D.base D.weight D.support n =
      (intPolynomialValue D.weight n : ℝ) *
        (supportDigitInt D.support n : ℝ) / (D.base : ℝ) ^ n := by
  by_cases hn : n ∈ D.support <;>
    simp [integralWeightedTerm, supportDigitInt, hn]

theorem finiteCarrySum_cast (D : CarrySeries) (N : ℕ) :
    ((∑ n ∈ Finset.Icc 0 N,
        intPolynomialValue D.weight n * supportDigitInt D.support n *
          (D.base : ℤ) ^ (N - n) : ℤ) : ℝ) =
      (D.base : ℝ) ^ N *
        ∑ n ∈ Finset.Icc 0 N,
          integralWeightedTerm D.base D.weight D.support n := by
  rw [Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  push_cast
  rw [integralWeightedTerm_eq]
  have hbase : (D.base : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) D.base_ge_two))
  have hpow : (D.base : ℝ) ^ (N - n) * (D.base : ℝ) ^ n =
      (D.base : ℝ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  field_simp
  rw [← hpow]
  ring

theorem carry_cast_eq_partial (D : CarrySeries) (N : ℕ) :
    (D.carry N : ℝ) =
      (D.denominator : ℝ) * (D.base : ℝ) ^ N *
        ((D.value : ℝ) -
          ∑ n ∈ Finset.Icc 0 N,
            integralWeightedTerm D.base D.weight D.support n) := by
  unfold carry
  push_cast
  have hfinite := finiteCarrySum_cast D N
  push_cast at hfinite
  rw [hfinite]
  have hden : (D.denominator : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt D.denominator_pos)
  rw [Rat.cast_def]
  change
    (D.value.num : ℝ) * (D.base : ℝ) ^ N -
        (D.value.den : ℝ) *
          ((D.base : ℝ) ^ N *
            ∑ n ∈ Finset.Icc 0 N,
              integralWeightedTerm D.base D.weight D.support n) =
      (D.value.den : ℝ) * (D.base : ℝ) ^ N *
        ((D.value.num : ℝ) / (D.value.den : ℝ) -
          ∑ n ∈ Finset.Icc 0 N,
            integralWeightedTerm D.base D.weight D.support n)
  have hden' : (D.value.den : ℝ) ≠ 0 := by
    change (D.denominator : ℝ) ≠ 0
    exact hden
  field_simp [hden']

/-- Scaled tail summand whose sum is the carry. -/
def tailTerm (D : CarrySeries) (N j : ℕ) : ℝ :=
  (D.denominator : ℝ) * (D.base : ℝ) ^ N *
    integralWeightedTerm D.base D.weight D.support (j + (N + 1))

/-- A summable, support-independent majorant for `tailTerm`. -/
def tailMajorant (D : CarrySeries) (N j : ℕ) : ℝ :=
  (D.denominator : ℝ) * polynomialCoefficientMass D.weight *
    (N + 1 : ℝ) ^ D.weight.natDegree *
      ((j + 2 : ℝ) ^ D.weight.natDegree /
        (D.base : ℝ) ^ (j + 1))

theorem sum_Icc_zero_eq_sum_range (D : CarrySeries) (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N,
        integralWeightedTerm D.base D.weight D.support n =
      ∑ n ∈ Finset.range (N + 1),
        integralWeightedTerm D.base D.weight D.support n := by
  congr 1
  ext n
  simp

theorem tail_hasSum (D : CarrySeries) (N : ℕ) :
    HasSum (D.tailTerm N) (D.carry N : ℝ) := by
  have htail := (hasSum_nat_add_iff'
    (f := integralWeightedTerm D.base D.weight D.support) (N + 1)).mpr D.hasSum
  rw [← D.sum_Icc_zero_eq_sum_range N] at htail
  have hscaled := htail.mul_left
    ((D.denominator : ℝ) * (D.base : ℝ) ^ N)
  rw [← D.carry_cast_eq_partial N] at hscaled
  unfold tailTerm
  simpa only [mul_assoc] using hscaled

theorem exists_support_gt (D : CarrySeries) (N : ℕ) :
    ∃ n ∈ D.support, N < n := by
  by_contra h
  push Not at h
  have hsubset : D.support ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (h n hn)
  exact D.support_infinite ((Finset.range (N + 1)).finite_toSet.subset hsubset)

theorem tailTerm_nonneg (D : CarrySeries) {N : ℕ}
    (hN : D.positiveFrom ≤ N) (j : ℕ) : 0 ≤ D.tailTerm N j := by
  have hbpos : (0 : ℝ) < D.base := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) D.base_ge_two)
  have hindex : D.positiveFrom ≤ j + (N + 1) := by omega
  by_cases hj : j + (N + 1) ∈ D.support
  · have hw : 0 < intPolynomialValue D.weight (j + (N + 1)) :=
      D.weight_pos _ hindex
    unfold tailTerm integralWeightedTerm
    rw [if_pos hj]
    positivity
  · simp [tailTerm, integralWeightedTerm, hj]

theorem tailTerm_pos_of_mem (D : CarrySeries) {N j : ℕ}
    (hN : D.positiveFrom ≤ N) (hj : j + (N + 1) ∈ D.support) :
    0 < D.tailTerm N j := by
  have hbpos : (0 : ℝ) < D.base := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) D.base_ge_two)
  have hindex : D.positiveFrom ≤ j + (N + 1) := by omega
  have hw : 0 < intPolynomialValue D.weight (j + (N + 1)) :=
    D.weight_pos _ hindex
  unfold tailTerm integralWeightedTerm
  rw [if_pos hj]
  have hwReal : (0 : ℝ) < intPolynomialValue D.weight (j + (N + 1)) := by
    exact_mod_cast hw
  exact mul_pos
    (mul_pos (by exact_mod_cast D.denominator_pos) (pow_pos hbpos _))
    (div_pos hwReal (pow_pos hbpos _))

theorem carry_pos (D : CarrySeries) {N : ℕ}
    (hN : D.positiveFrom ≤ N) : 0 < D.carry N := by
  obtain ⟨n, hnS, hnN⟩ := D.exists_support_gt N
  let j := n - (N + 1)
  have hindex : j + (N + 1) = n := by
    dsimp [j]
    omega
  have hjS : j + (N + 1) ∈ D.support := by simpa only [hindex] using hnS
  have htermPos : 0 < D.tailTerm N j := D.tailTerm_pos_of_mem hN hjS
  have hsum := D.tail_hasSum N
  have htermLe : D.tailTerm N j ≤ (D.carry N : ℝ) := by
    rw [← hsum.tsum_eq]
    simpa using hsum.summable.sum_le_tsum {j}
      (fun i _ => D.tailTerm_nonneg hN i)
  have hcarryReal : (0 : ℝ) < D.carry N := htermPos.trans_le htermLe
  exact_mod_cast hcarryReal

theorem one_le_carry (D : CarrySeries) {N : ℕ}
    (hN : D.positiveFrom ≤ N) : 1 ≤ D.carry N := by
  have hpos := D.carry_pos hN
  omega

theorem tailTerm_le_majorant (D : CarrySeries) (N j : ℕ) :
    D.tailTerm N j ≤ D.tailMajorant N j := by
  have hden : (0 : ℝ) ≤ D.denominator := by positivity
  have hscaled := scaled_integralWeightedTerm_abs_le D.base_ge_two
    D.weight D.support N j
  unfold tailTerm tailMajorant
  calc
    (D.denominator : ℝ) * (D.base : ℝ) ^ N *
        integralWeightedTerm D.base D.weight D.support (j + (N + 1)) ≤
      (D.denominator : ℝ) * (D.base : ℝ) ^ N *
          |integralWeightedTerm D.base D.weight D.support (j + (N + 1))| := by
      have hself := le_abs_self
        (integralWeightedTerm D.base D.weight D.support (j + (N + 1)))
      exact mul_le_mul_of_nonneg_left hself
        (mul_nonneg hden (by positivity))
    _ = (D.denominator : ℝ) *
        ((D.base : ℝ) ^ N *
          |integralWeightedTerm D.base D.weight D.support (j + (N + 1))|) := by
      ring
    _ ≤ (D.denominator : ℝ) *
        (polynomialCoefficientMass D.weight *
          (N + 1 : ℝ) ^ D.weight.natDegree *
            ((j + 2 : ℝ) ^ D.weight.natDegree /
              (D.base : ℝ) ^ (j + 1))) := by
      gcongr
    _ = (D.denominator : ℝ) * polynomialCoefficientMass D.weight *
        (N + 1 : ℝ) ^ D.weight.natDegree *
          ((j + 2 : ℝ) ^ D.weight.natDegree /
            (D.base : ℝ) ^ (j + 1)) := by ring

theorem tailMajorant_hasSum (D : CarrySeries) (N : ℕ) :
    HasSum (D.tailMajorant N)
      ((D.denominator : ℝ) * polynomialCoefficientMass D.weight *
        (N + 1 : ℝ) ^ D.weight.natDegree *
          geometricMoment D.base D.weight.natDegree) := by
  have hs : HasSum
      (fun j : ℕ => (j + 2 : ℝ) ^ D.weight.natDegree /
        (D.base : ℝ) ^ (j + 1))
      (geometricMoment D.base D.weight.natDegree) := by
    unfold geometricMoment
    exact (summable_geometricMoment_term
      (d := D.weight.natDegree) D.base_ge_two).hasSum
  have hscaled := hs.mul_left
    ((D.denominator : ℝ) * polynomialCoefficientMass D.weight *
      (N + 1 : ℝ) ^ D.weight.natDegree)
  unfold tailMajorant
  simpa only [mul_assoc] using hscaled

/-- The explicit polynomial-height constant for the carry. -/
def heightConstant (D : CarrySeries) : ℝ :=
  (D.denominator : ℝ) * polynomialCoefficientMass D.weight *
    geometricMoment D.base D.weight.natDegree

theorem heightConstant_pos (D : CarrySeries) : 0 < D.heightConstant := by
  have hmoment : 0 < geometricMoment D.base D.weight.natDegree := by
    have hs := summable_geometricMoment_term
      (d := D.weight.natDegree) D.base_ge_two
    have hzero :
        (0 + 2 : ℝ) ^ D.weight.natDegree /
            (D.base : ℝ) ^ (0 + 1) ≤
          geometricMoment D.base D.weight.natDegree := by
      unfold geometricMoment
      simpa using hs.sum_le_tsum {0} (fun j _ => by positivity)
    have hbpos : (0 : ℝ) < D.base := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) D.base_ge_two)
    have hfirst :
        0 < (0 + 2 : ℝ) ^ D.weight.natDegree /
          (D.base : ℝ) ^ (0 + 1) :=
      div_pos (by positivity) (pow_pos hbpos _)
    exact hfirst.trans_le hzero
  unfold heightConstant
  have hden : (0 : ℝ) < D.denominator := by
    exact_mod_cast D.denominator_pos
  exact mul_pos
    (mul_pos hden (polynomialCoefficientMass_pos D.weight_ne_zero)) hmoment

theorem carry_height (D : CarrySeries) {N : ℕ}
    (_hN : D.positiveFrom ≤ N) :
    (D.carry N : ℝ) ≤
      D.heightConstant * (N + 1 : ℝ) ^ D.weight.natDegree := by
  have hcarry := D.tail_hasSum N
  have hmajor := D.tailMajorant_hasSum N
  have hle := hcarry.summable.tsum_le_tsum
    (fun j => D.tailTerm_le_majorant N j) hmajor.summable
  rw [hcarry.tsum_eq, hmajor.tsum_eq] at hle
  unfold heightConstant
  nlinarith

/-- A positive natural coefficient dominating the real carry-height
constant. -/
def heightNatConstant (D : CarrySeries) : ℕ :=
  Nat.ceil D.heightConstant + 1

theorem heightNatConstant_pos (D : CarrySeries) :
    0 < D.heightNatConstant := by
  simp [heightNatConstant]

/-- Natural-number form of the polynomial carry-height bound. -/
theorem carry_natAbs_le (D : CarrySeries) {N : ℕ}
    (hN : D.positiveFrom ≤ N) :
    (D.carry N).natAbs ≤
      D.heightNatConstant * (N + 1) ^ D.weight.natDegree := by
  have hcarryPos : 0 < D.carry N := D.carry_pos hN
  have habsCast : (((D.carry N).natAbs : ℕ) : ℝ) = (D.carry N : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos]
    exact_mod_cast hcarryPos
  have hconstant : D.heightConstant ≤ (D.heightNatConstant : ℝ) := by
    exact (Nat.le_ceil D.heightConstant).trans
      (by exact_mod_cast Nat.le_add_right (Nat.ceil D.heightConstant) 1)
  have hreal : (((D.carry N).natAbs : ℕ) : ℝ) ≤
      ((D.heightNatConstant * (N + 1) ^ D.weight.natDegree : ℕ) : ℝ) := by
    rw [habsCast]
    push_cast
    exact (D.carry_height hN).trans
      (mul_le_mul_of_nonneg_right hconstant (by positivity))
  exact_mod_cast hreal

/-- Exact logarithmic-scale domination: a fixed polynomial quantity is
strictly smaller than one explicit power of any base at least two.  This
avoids hidden `O`-notation in the locking and continuation cutoffs. -/
theorem polynomial_lt_base_pow_logScale {b : ℕ} (hb : 2 ≤ b)
    (C X a : ℕ) :
    C * X ^ a <
      b ^ (Nat.clog b (C + 1) + a * (Nat.log b X + 1)) := by
  have hbOne : 1 < b := by omega
  have hC : C + 1 ≤ b ^ Nat.clog b (C + 1) :=
    Nat.le_pow_clog hbOne (C + 1)
  have hX : X + 1 ≤ b ^ (Nat.log b X + 1) := by
    exact (Nat.lt_pow_succ_log_self hbOne X)
  have hpow : (X + 1) ^ a ≤ (b ^ (Nat.log b X + 1)) ^ a :=
    Nat.pow_le_pow_left hX a
  calc
    C * X ^ a ≤ C * (X + 1) ^ a := by
      gcongr
      omega
    _ < (C + 1) * (X + 1) ^ a := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self C) (by positivity)
    _ ≤ b ^ Nat.clog b (C + 1) *
          (b ^ (Nat.log b X + 1)) ^ a := Nat.mul_le_mul hC hpow
    _ = b ^ (Nat.clog b (C + 1) + a * (Nat.log b X + 1)) := by
      rw [← pow_mul, ← pow_add]
      rw [Nat.mul_comm (Nat.log b X + 1) a]

/-- Exact base-`b` carry recurrence. -/
theorem carry_succ (D : CarrySeries) (N : ℕ) :
    D.carry (N + 1) =
      (D.base : ℤ) * D.carry N -
        (D.denominator : ℤ) * intPolynomialValue D.weight (N + 1) *
          supportDigitInt D.support (N + 1) := by
  have hsum :
      (∑ n ∈ Finset.Icc 0 (N + 1),
          intPolynomialValue D.weight n * supportDigitInt D.support n *
            (D.base : ℤ) ^ (N + 1 - n)) =
        (D.base : ℤ) *
            ∑ n ∈ Finset.Icc 0 N,
              intPolynomialValue D.weight n * supportDigitInt D.support n *
                (D.base : ℤ) ^ (N - n) +
          intPolynomialValue D.weight (N + 1) *
            supportDigitInt D.support (N + 1) := by
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hold :
        (∑ n ∈ Finset.Icc 0 N,
            intPolynomialValue D.weight n * supportDigitInt D.support n *
              (D.base : ℤ) ^ (N + 1 - n)) =
          (D.base : ℤ) *
            ∑ n ∈ Finset.Icc 0 N,
              intPolynomialValue D.weight n * supportDigitInt D.support n *
                (D.base : ℤ) ^ (N - n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hexponent : N + 1 - n = (N - n) + 1 := by omega
      rw [hexponent, pow_succ]
      ring
    rw [hold]
    norm_num
  unfold carry
  rw [hsum, pow_succ]
  ring

/-- A genuine gap between consecutive support points. -/
def IsSupportGap (D : CarrySeries) (x g : ℕ) : Prop :=
  0 < g ∧ x ∈ D.support ∧ x + g ∈ D.support ∧
    ∀ n, x < n → n < x + g → n ∉ D.support

theorem carry_inside_gap (D : CarrySeries) (x g : ℕ)
    (hgap : D.IsSupportGap x g) :
    ∀ r < g, D.carry (x + r) = (D.base : ℤ) ^ r * D.carry x := by
  intro r hr
  induction r with
  | zero => simp
  | succ r ih =>
      have hrg : r < g := r.lt_succ_self.trans hr
      have hnotmem : x + (r + 1) ∉ D.support := by
        apply hgap.2.2.2 (x + (r + 1))
        · omega
        · omega
      have hnotmem' : x + r + 1 ∉ D.support := by
        simpa [Nat.add_assoc] using hnotmem
      rw [show x + (r + 1) = (x + r) + 1 by omega,
        D.carry_succ, ih hrg]
      simp [supportDigitInt, hnotmem', pow_succ]
      ring

/-- Exponential lower bound inside a support gap, compared with the global
polynomial carry height. -/
theorem gap_power_bound (D : CarrySeries) {x g : ℕ}
    (hx : D.positiveFrom ≤ x) (hgap : D.IsSupportGap x g) :
    (D.base : ℝ) ^ (g - 1) ≤
      D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree := by
  have hg : 0 < g := hgap.1
  have hiterate := D.carry_inside_gap x g hgap (g - 1) (by omega)
  have hpositive : 1 ≤ D.carry x := D.one_le_carry hx
  have hcutoff : D.positiveFrom ≤ x + (g - 1) := hx.trans (Nat.le_add_right _ _)
  have hupper := D.carry_height hcutoff
  have hbase_nonneg : (0 : ℝ) ≤ D.base := by positivity
  have hpow_nonneg : (0 : ℝ) ≤ (D.base : ℝ) ^ (g - 1) := by positivity
  have hpositiveReal : (1 : ℝ) ≤ D.carry x := by exact_mod_cast hpositive
  have hiterateReal :
      (D.carry (x + (g - 1)) : ℝ) =
        (D.base : ℝ) ^ (g - 1) * (D.carry x : ℝ) := by
    exact_mod_cast hiterate
  calc
    (D.base : ℝ) ^ (g - 1) ≤
        (D.base : ℝ) ^ (g - 1) * (D.carry x : ℝ) := by
      nlinarith
    _ = (D.carry (x + (g - 1)) : ℝ) := hiterateReal.symm
    _ ≤ D.heightConstant *
        (((x + (g - 1) : ℕ) : ℝ) + 1) ^
          D.weight.natDegree := hupper
    _ = D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree := by
      congr 2
      exact_mod_cast (show x + (g - 1) + 1 = x + g by omega)

/-- Exponential growth eventually dominates the polynomial carry envelope. -/
theorem eventually_gapPolynomial_lt_basePow (D : CarrySeries) :
    ∃ x₀ : ℕ, ∀ n : ℕ, x₀ ≤ n →
      D.heightConstant * (2 : ℝ) ^ D.weight.natDegree *
          (n : ℝ) ^ D.weight.natDegree <
        (D.base : ℝ) ^ (n - 1) := by
  let K : ℝ := D.heightConstant * (2 : ℝ) ^ D.weight.natDegree
  have hbReal : (1 : ℝ) < D.base := by exact_mod_cast D.base_ge_two
  have hbpos : (0 : ℝ) < D.base := zero_lt_one.trans hbReal
  have ht :=
    (tendsto_pow_const_div_const_pow_of_one_lt
      D.weight.natDegree hbReal).const_mul (K * (D.base : ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      K * (D.base : ℝ) *
          ((n : ℝ) ^ D.weight.natDegree /
            (D.base : ℝ) ^ n) < 1 :=
    (tendsto_order.1 ht).2 1 (by norm_num)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hevent
  refine ⟨max x₀ 1, ?_⟩
  intro n hn
  have hnx₀ : x₀ ≤ n := (le_max_left x₀ 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right x₀ 1).trans hn
  have h := hx₀ n hnx₀
  have hden : 0 < (D.base : ℝ) ^ n := pow_pos hbpos _
  have hraw :
      K * (D.base : ℝ) * (n : ℝ) ^ D.weight.natDegree <
        (D.base : ℝ) ^ n := by
    apply (div_lt_one hden).mp
    calc
      (K * (D.base : ℝ) * (n : ℝ) ^ D.weight.natDegree) /
          (D.base : ℝ) ^ n =
        K * (D.base : ℝ) *
          ((n : ℝ) ^ D.weight.natDegree / (D.base : ℝ) ^ n) := by ring
      _ < 1 := h
  have hpow :
      (D.base : ℝ) ^ n =
        (D.base : ℝ) ^ (n - 1) * (D.base : ℝ) := by
    calc
      (D.base : ℝ) ^ n = (D.base : ℝ) ^ ((n - 1) + 1) := by
        congr 1
        omega
      _ = (D.base : ℝ) ^ (n - 1) * (D.base : ℝ) := by rw [pow_succ]
  rw [hpow] at hraw
  have hcancel :
      K * (n : ℝ) ^ D.weight.natDegree <
        (D.base : ℝ) ^ (n - 1) := by
    nlinarith
  simpa only [K] using hcancel

theorem eventually_gap_lt_anchor (D : CarrySeries) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g → g < x := by
  obtain ⟨xexp, hexp⟩ := D.eventually_gapPolynomial_lt_basePow
  refine ⟨max D.positiveFrom xexp, ?_⟩
  intro x hx g hgap
  have hxcut : D.positiveFrom ≤ x := (le_max_left _ _).trans hx
  have hxxexp : xexp ≤ x := (le_max_right _ _).trans hx
  by_contra hnot
  have hxg : x ≤ g := Nat.le_of_not_gt hnot
  have hgexp : xexp ≤ g := hxxexp.trans hxg
  have hpower := D.gap_power_bound hxcut hgap
  have hsumNat : x + g ≤ 2 * g := by omega
  have hsumReal : (x + g : ℝ) ≤ 2 * (g : ℝ) := by exact_mod_cast hsumNat
  have hheightNonneg : 0 ≤ D.heightConstant := D.heightConstant_pos.le
  have hpoly :
      D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree ≤
        D.heightConstant * (2 : ℝ) ^ D.weight.natDegree *
          (g : ℝ) ^ D.weight.natDegree := by
    calc
      D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree ≤
          D.heightConstant * (2 * (g : ℝ)) ^ D.weight.natDegree := by
        gcongr
      _ = D.heightConstant * (2 : ℝ) ^ D.weight.natDegree *
          (g : ℝ) ^ D.weight.natDegree := by
        rw [mul_pow]
        ring
  have hstrict := hexp g hgexp
  exact (not_lt_of_ge (hpower.trans hpoly)) hstrict

/-- Integer coefficient used to turn the real carry envelope into a natural
power comparison. -/
def gapCoefficient (D : CarrySeries) : ℕ :=
  Nat.ceil (D.heightConstant * (2 : ℝ) ^ D.weight.natDegree)

theorem gapCoefficient_pos (D : CarrySeries) : 0 < D.gapCoefficient := by
  apply Nat.ceil_pos.mpr
  exact mul_pos D.heightConstant_pos (by positivity)

/-- Paper label `lem:carries`: the logarithmic gap conclusion. -/
theorem eventual_gap_log_bound (D : CarrySeries) :
    ∃ Cgap x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g →
        g ≤ D.weight.natDegree * Nat.log D.base x + Cgap := by
  obtain ⟨xanchor, hanchor⟩ := D.eventually_gap_lt_anchor
  let C : ℕ := D.gapCoefficient
  let Cgap : ℕ :=
    Nat.clog D.base C + D.weight.natDegree + 1
  refine ⟨Cgap, max xanchor D.positiveFrom, ?_⟩
  intro x hx g hgap
  have hxanchor : xanchor ≤ x := (le_max_left _ _).trans hx
  have hxcut : D.positiveFrom ≤ x := (le_max_right _ _).trans hx
  have hgltx : g < x := hanchor x hxanchor g hgap
  have hpower := D.gap_power_bound hxcut hgap
  have hsumNat : x + g ≤ 2 * x := by omega
  have hsumReal : (x + g : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hsumNat
  have hpoly :
      D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree ≤
        (C : ℝ) * (x : ℝ) ^ D.weight.natDegree := by
    have hceil :
        D.heightConstant * (2 : ℝ) ^ D.weight.natDegree ≤ (C : ℝ) := by
      exact Nat.le_ceil _
    calc
      D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree ≤
          D.heightConstant * (2 * (x : ℝ)) ^ D.weight.natDegree := by
        gcongr
        exact D.heightConstant_pos.le
      _ = (D.heightConstant * (2 : ℝ) ^ D.weight.natDegree) *
          (x : ℝ) ^ D.weight.natDegree := by
        rw [mul_pow]
        ring
      _ ≤ (C : ℝ) * (x : ℝ) ^ D.weight.natDegree := by
        gcongr
  have hnatural :
      D.base ^ (g - 1) ≤ C * x ^ D.weight.natDegree := by
    exact_mod_cast hpower.trans hpoly
  have hbNat : 1 < D.base := lt_of_lt_of_le (by omega) D.base_ge_two
  have hCpos : 0 < C := by
    dsimp [C]
    exact D.gapCoefficient_pos
  have hCpow : C ≤ D.base ^ Nat.clog D.base C :=
    Nat.le_pow_clog hbNat C
  have hxpow : x < D.base ^ (Nat.log D.base x + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hbNat x
  have hxpowLe :
      x ^ D.weight.natDegree ≤
        (D.base ^ (Nat.log D.base x + 1)) ^ D.weight.natDegree := by
    exact Nat.pow_le_pow_left hxpow.le _
  have hproduct :
      C * x ^ D.weight.natDegree ≤
        D.base ^ Nat.clog D.base C *
          (D.base ^ (Nat.log D.base x + 1)) ^ D.weight.natDegree :=
    Nat.mul_le_mul hCpow hxpowLe
  have hpowers :
      D.base ^ (g - 1) ≤
        D.base ^
          (Nat.clog D.base C +
            D.weight.natDegree * (Nat.log D.base x + 1)) := by
    calc
      D.base ^ (g - 1) ≤ C * x ^ D.weight.natDegree := hnatural
      _ ≤ D.base ^ Nat.clog D.base C *
          (D.base ^ (Nat.log D.base x + 1)) ^ D.weight.natDegree := hproduct
      _ = D.base ^
          (Nat.clog D.base C +
            D.weight.natDegree * (Nat.log D.base x + 1)) := by
        rw [← pow_mul, ← pow_add]
        simp only [Nat.mul_comm]
  have hexponent :
      g - 1 ≤ Nat.clog D.base C +
        D.weight.natDegree * (Nat.log D.base x + 1) :=
    (Nat.pow_le_pow_iff_right hbNat).mp hpowers
  have hgpos : 0 < g := hgap.1
  calc
    g = (g - 1) + 1 := by omega
    _ ≤ (Nat.clog D.base C +
          D.weight.natDegree * (Nat.log D.base x + 1)) + 1 :=
      Nat.add_le_add_right hexponent 1
    _ = D.weight.natDegree * Nat.log D.base x + Cgap := by
      dsimp [Cgap]
      ring

/-- Bundled form of all conclusions of `lem:carries`. -/
theorem lem_carries (D : CarrySeries) :
    (∀ N, D.carry (N + 1) =
      (D.base : ℤ) * D.carry N -
        (D.denominator : ℤ) * intPolynomialValue D.weight (N + 1) *
          supportDigitInt D.support (N + 1)) ∧
    (∀ N, D.positiveFrom ≤ N → 1 ≤ D.carry N) ∧
    (∀ N, D.positiveFrom ≤ N →
      (D.carry N : ℝ) ≤
        D.heightConstant * (N + 1 : ℝ) ^ D.weight.natDegree) ∧
    (∃ Cgap x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g →
        g ≤ D.weight.natDegree * Nat.log D.base x + Cgap) := by
  refine ⟨D.carry_succ, ?_, ?_, D.eventual_gap_log_bound⟩
  · intro N hN
    exact D.one_le_carry hN
  · intro N hN
    exact D.carry_height hN

end CarrySeries

end Erdos260.PolynomialWindow
