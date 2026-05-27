import Mathlib

/-!
# Carry recurrence

This file formalizes the algebraic carry identity used in Section 21 of
`proof_v2.tex`.  The finite prefix is indexed by `range N`, so
`weightedPartialSum d N` is the sum over `1 <= n <= N`.
-/

namespace Erdos260

noncomputable section

/-- A rational-valued digit sequence whose values are only `0` and `1`. -/
def RatBinaryDigits (d : Nat -> Rat) : Prop :=
  forall n, d n = 0 \/ d n = 1

/-- The weighted finite prefix `sum_{1 <= n <= N} n d_n / 2^n`. -/
def weightedPartialSum (d : Nat -> Rat) (N : Nat) : Rat :=
  ∑ i ∈ Finset.range N, ((i + 1 : Nat) : Rat) * d (i + 1) / (2 : Rat) ^ (i + 1)

/-- The finite weighted tail from prefix length `N` up to, but not including, `M`. -/
def weightedTail (d : Nat -> Rat) (N M : Nat) : Rat :=
  ∑ i ∈ Finset.Ico N M, ((i + 1 : Nat) : Rat) * d (i + 1) / (2 : Rat) ^ (i + 1)

/-- The all-one weighted summand at index `i + 1`. -/
def weightedKernel (i : Nat) : Rat :=
  ((i + 1 : Nat) : Rat) / (2 : Rat) ^ (i + 1)

/-- The exact infinite all-one tail majorant from prefix length `N`. -/
def geometricTailMajorant (N : Nat) : Rat :=
  ((N + 2 : Nat) : Rat) / (2 : Rat) ^ N

/-- The finite carry attached to a rational target `eta`. -/
def carry (Q : Nat) (eta : Rat) (d : Nat -> Rat) (N : Nat) : Rat :=
  (Q : Rat) * (2 : Rat) ^ N * (eta - weightedPartialSum d N)

theorem RatBinaryDigits.nonneg {d : Nat -> Rat} (hd : RatBinaryDigits d) :
    forall n, 0 <= d n := by
  intro n
  rcases hd n with h | h <;> simp [h]

theorem RatBinaryDigits.le_one {d : Nat -> Rat} (hd : RatBinaryDigits d) :
    forall n, d n <= 1 := by
  intro n
  rcases hd n with h | h <;> simp [h]

@[simp]
theorem weightedPartialSum_zero (d : Nat -> Rat) :
    weightedPartialSum d 0 = 0 := by
  simp [weightedPartialSum]

theorem weightedPartialSum_succ (d : Nat -> Rat) (N : Nat) :
    weightedPartialSum d (N + 1) =
      weightedPartialSum d N + ((N + 1 : Nat) : Rat) * d (N + 1) / (2 : Rat) ^ (N + 1) := by
  simp [weightedPartialSum, Finset.sum_range_succ]

@[simp]
theorem weightedTail_self (d : Nat -> Rat) (N : Nat) :
    weightedTail d N N = 0 := by
  simp [weightedTail]

theorem weightedPartialSum_add_tail {d : Nat -> Rat} {N M : Nat} (hNM : N <= M) :
    weightedPartialSum d N + weightedTail d N M = weightedPartialSum d M := by
  unfold weightedPartialSum weightedTail
  exact Finset.sum_range_add_sum_Ico _ hNM

theorem weightedPartialSum_sub_eq_tail {d : Nat -> Rat} {N M : Nat} (hNM : N <= M) :
    weightedPartialSum d M - weightedPartialSum d N = weightedTail d N M := by
  have h := weightedPartialSum_add_tail (d := d) hNM
  linarith

theorem weightedTail_succ_right (d : Nat -> Rat) {N M : Nat} (hNM : N <= M) :
    weightedTail d N (M + 1) =
      weightedTail d N M + ((M + 1 : Nat) : Rat) * d (M + 1) / (2 : Rat) ^ (M + 1) := by
  unfold weightedTail
  rw [Finset.sum_Ico_succ_top hNM]

theorem weightedKernel_telescope (i : Nat) :
    weightedKernel i = geometricTailMajorant i - geometricTailMajorant (i + 1) := by
  unfold weightedKernel geometricTailMajorant
  field_simp [pow_succ]
  norm_num [Nat.cast_add]
  ring

theorem weightedKernel_sum_Ico_eq {N M : Nat} (hNM : N <= M) :
    (∑ i ∈ Finset.Ico N M, weightedKernel i) =
      geometricTailMajorant N - geometricTailMajorant M := by
  induction M with
  | zero =>
      have hN0 : N = 0 := by omega
      subst N
      simp [geometricTailMajorant]
  | succ M ih =>
      by_cases hN : N <= M
      · rw [Finset.sum_Ico_succ_top hN, ih hN, weightedKernel_telescope]
        ring
      · have hNsucc : N = M + 1 := by omega
        subst N
        simp [geometricTailMajorant]

theorem geometricTailMajorant_nonneg (N : Nat) :
    0 <= geometricTailMajorant N := by
  unfold geometricTailMajorant
  positivity

theorem weightedTail_nonneg {d : Nat -> Rat} (hd0 : forall n, 0 <= d n) (N M : Nat) :
    0 <= weightedTail d N M := by
  unfold weightedTail
  exact Finset.sum_nonneg fun i _ => by
    have hden : 0 < (2 : Rat) ^ (i + 1) := by positivity
    exact div_nonneg (mul_nonneg (by positivity) (hd0 (i + 1))) hden.le

theorem weightedTail_le_kernelTail {d : Nat -> Rat}
    (hd1 : forall n, d n <= 1) (N M : Nat) :
    weightedTail d N M <= ∑ i ∈ Finset.Ico N M, weightedKernel i := by
  unfold weightedTail weightedKernel
  exact Finset.sum_le_sum fun i _ => by
    have hden : 0 < (2 : Rat) ^ (i + 1) := by positivity
    have hnum : 0 <= ((i + 1 : Nat) : Rat) := by positivity
    calc
      ((i + 1 : Nat) : Rat) * d (i + 1) / (2 : Rat) ^ (i + 1)
          <= ((i + 1 : Nat) : Rat) * 1 / (2 : Rat) ^ (i + 1) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hd1 (i + 1)) hnum) hden.le
      _ = ((i + 1 : Nat) : Rat) / (2 : Rat) ^ (i + 1) := by ring

theorem weightedTail_le_majorant {d : Nat -> Rat}
    (hd1 : forall n, d n <= 1) {N M : Nat} (hNM : N <= M) :
    weightedTail d N M <= geometricTailMajorant N := by
  calc
    weightedTail d N M <= ∑ i ∈ Finset.Ico N M, weightedKernel i :=
      weightedTail_le_kernelTail hd1 N M
    _ = geometricTailMajorant N - geometricTailMajorant M :=
      weightedKernel_sum_Ico_eq hNM
    _ <= geometricTailMajorant N := by
      have hM := geometricTailMajorant_nonneg M
      linarith

@[simp]
theorem carry_zero (Q : Nat) (eta : Rat) (d : Nat -> Rat) :
    carry Q eta d 0 = (Q : Rat) * eta := by
  simp [carry]

/-- The carry recurrence (formula (21.1) in `proof_v2.tex`). -/
theorem carry_succ (Q : Nat) (eta : Rat) (d : Nat -> Rat) (N : Nat) :
    carry Q eta d (N + 1) =
      2 * carry Q eta d N - (Q : Rat) * ((N + 1 : Nat) : Rat) * d (N + 1) := by
  unfold carry
  rw [weightedPartialSum_succ]
  field_simp [pow_succ]
  ring

theorem carry_finite_target {Q N M : Nat} {d : Nat -> Rat} (hNM : N <= M) :
    carry Q (weightedPartialSum d M) d N =
      (Q : Rat) * (2 : Rat) ^ N * weightedTail d N M := by
  unfold carry
  rw [weightedPartialSum_sub_eq_tail (d := d) hNM]

theorem carry_finite_target_nonneg {Q N M : Nat} {d : Nat -> Rat}
    (hd0 : forall n, 0 <= d n) (hNM : N <= M) :
    0 <= carry Q (weightedPartialSum d M) d N := by
  rw [carry_finite_target (Q := Q) (d := d) hNM]
  exact mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    (weightedTail_nonneg hd0 N M)

theorem carry_finite_target_le {Q N M : Nat} {d : Nat -> Rat}
    (hd1 : forall n, d n <= 1) (hNM : N <= M) :
    carry Q (weightedPartialSum d M) d N <= (Q : Rat) * ((N + 2 : Nat) : Rat) := by
  rw [carry_finite_target (Q := Q) (d := d) hNM]
  have htail := weightedTail_le_majorant hd1 hNM
  have hfactor : 0 <= (Q : Rat) * (2 : Rat) ^ N := by positivity
  calc
    (Q : Rat) * (2 : Rat) ^ N * weightedTail d N M
        <= (Q : Rat) * (2 : Rat) ^ N * geometricTailMajorant N := by
          exact mul_le_mul_of_nonneg_left htail hfactor
    _ = (Q : Rat) * ((N + 2 : Nat) : Rat) := by
      unfold geometricTailMajorant
      field_simp

/--
Finite analogue of the carry bound (21.2): if the target is a later finite
prefix of a binary digit sequence, then the carry at an earlier prefix is between
`0` and `Q (N+2)`.
-/
theorem carry_finite_target_bounds_of_binary {Q N M : Nat} {d : Nat -> Rat}
    (hd : RatBinaryDigits d) (hNM : N <= M) :
    0 <= carry Q (weightedPartialSum d M) d N /\
      carry Q (weightedPartialSum d M) d N <= (Q : Rat) * ((N + 2 : Nat) : Rat) :=
  ⟨carry_finite_target_nonneg hd.nonneg hNM,
    carry_finite_target_le hd.le_one hNM⟩

end

end Erdos260
