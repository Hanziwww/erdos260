import Mathlib

/-!
# Real carry bounds

This file lifts the finite carry estimates from `Erdos260.Carry` to real-valued
targets and closes the corresponding infinite-series carry bound.  The indexing
matches `proof_v2.tex`: `realWeightedPartialSum d N` sums over `1 <= n <= N`.
-/

namespace Erdos260

noncomputable section

open scoped Topology

/-- A real-valued digit sequence whose values are only `0` and `1`. -/
def RealBinaryDigits (d : Nat -> ℝ) : Prop :=
  forall n, d n = 0 \/ d n = 1

/-- The weighted real summand at index `i + 1`. -/
def realWeightedTerm (d : Nat -> ℝ) (i : Nat) : ℝ :=
  ((i + 1 : Nat) : ℝ) * d (i + 1) / (2 : ℝ) ^ (i + 1)

/-- The infinite weighted real value `sum_{n >= 1} n d_n / 2^n`, as a `tsum`. -/
def realWeightedValue (d : Nat -> ℝ) : ℝ :=
  ∑' i : Nat, realWeightedTerm d i

/-- The weighted finite prefix `sum_{1 <= n <= N} n d_n / 2^n`. -/
def realWeightedPartialSum (d : Nat -> ℝ) (N : Nat) : ℝ :=
  ∑ i ∈ Finset.range N, realWeightedTerm d i

/-- The finite weighted tail from prefix length `N` up to, but not including, `M`. -/
def realWeightedTail (d : Nat -> ℝ) (N M : Nat) : ℝ :=
  ∑ i ∈ Finset.Ico N M, realWeightedTerm d i

/-- The all-one weighted real summand at index `i + 1`. -/
def realWeightedKernel (i : Nat) : ℝ :=
  ((i + 1 : Nat) : ℝ) / (2 : ℝ) ^ (i + 1)

/-- The exact infinite all-one real tail majorant from prefix length `N`. -/
def realGeometricTailMajorant (N : Nat) : ℝ :=
  ((N + 2 : Nat) : ℝ) / (2 : ℝ) ^ N

/-- The real carry attached to a target `eta`. -/
def realCarry (Q : Nat) (eta : ℝ) (d : Nat -> ℝ) (N : Nat) : ℝ :=
  (Q : ℝ) * (2 : ℝ) ^ N * (eta - realWeightedPartialSum d N)

theorem RealBinaryDigits.nonneg {d : Nat -> ℝ} (hd : RealBinaryDigits d) :
    forall n, 0 <= d n := by
  intro n
  rcases hd n with h | h <;> simp [h]

theorem RealBinaryDigits.le_one {d : Nat -> ℝ} (hd : RealBinaryDigits d) :
    forall n, d n <= 1 := by
  intro n
  rcases hd n with h | h <;> simp [h]

@[simp]
theorem realWeightedPartialSum_zero (d : Nat -> ℝ) :
    realWeightedPartialSum d 0 = 0 := by
  simp [realWeightedPartialSum]

theorem realWeightedPartialSum_succ (d : Nat -> ℝ) (N : Nat) :
    realWeightedPartialSum d (N + 1) =
      realWeightedPartialSum d N + realWeightedTerm d N := by
  simp [realWeightedPartialSum, realWeightedTerm, Finset.sum_range_succ]

@[simp]
theorem realWeightedTail_self (d : Nat -> ℝ) (N : Nat) :
    realWeightedTail d N N = 0 := by
  simp [realWeightedTail]

theorem realWeightedPartialSum_add_tail {d : Nat -> ℝ} {N M : Nat} (hNM : N <= M) :
    realWeightedPartialSum d N + realWeightedTail d N M = realWeightedPartialSum d M := by
  unfold realWeightedPartialSum realWeightedTail
  exact Finset.sum_range_add_sum_Ico _ hNM

theorem realWeightedPartialSum_sub_eq_tail {d : Nat -> ℝ} {N M : Nat} (hNM : N <= M) :
    realWeightedPartialSum d M - realWeightedPartialSum d N = realWeightedTail d N M := by
  have h := realWeightedPartialSum_add_tail (d := d) hNM
  linarith

theorem realWeightedTail_succ_right (d : Nat -> ℝ) {N M : Nat} (hNM : N <= M) :
    realWeightedTail d N (M + 1) =
      realWeightedTail d N M + realWeightedTerm d M := by
  unfold realWeightedTail realWeightedTerm
  rw [Finset.sum_Ico_succ_top hNM]

theorem realWeightedKernel_telescope (i : Nat) :
    realWeightedKernel i = realGeometricTailMajorant i - realGeometricTailMajorant (i + 1) := by
  unfold realWeightedKernel realGeometricTailMajorant
  field_simp [pow_succ]
  norm_num [Nat.cast_add]
  ring

theorem realWeightedKernel_sum_Ico_eq {N M : Nat} (hNM : N <= M) :
    (∑ i ∈ Finset.Ico N M, realWeightedKernel i) =
      realGeometricTailMajorant N - realGeometricTailMajorant M := by
  induction M with
  | zero =>
      have hN0 : N = 0 := by omega
      subst N
      simp [realGeometricTailMajorant]
  | succ M ih =>
      by_cases hN : N <= M
      · rw [Finset.sum_Ico_succ_top hN, ih hN, realWeightedKernel_telescope]
        ring
      · have hNsucc : N = M + 1 := by omega
        subst N
        simp [realGeometricTailMajorant]

theorem realGeometricTailMajorant_nonneg (N : Nat) :
    0 <= realGeometricTailMajorant N := by
  unfold realGeometricTailMajorant
  positivity

theorem realWeightedKernel_summable :
    Summable realWeightedKernel := by
  have hf : Summable (fun n : Nat => (n : ℝ) * ((1 : ℝ) / 2) ^ n) := by
    exact (hasSum_coe_mul_geometric_of_norm_lt_one
      (r := ((1 : ℝ) / 2)) (by norm_num)).summable
  have hshift :
      Summable (fun n : Nat => ((n + 1 : Nat) : ℝ) * ((1 : ℝ) / 2) ^ (n + 1)) := by
    simpa using
      ((summable_nat_add_iff
        (f := fun n : Nat => (n : ℝ) * ((1 : ℝ) / 2) ^ n) 1).2 hf)
  convert hshift using 1
  ext n
  simp [realWeightedKernel, div_eq_mul_inv, inv_pow, Nat.cast_add]

theorem realWeightedTerm_nonneg {d : Nat -> ℝ} (hd0 : forall n, 0 <= d n) (i : Nat) :
    0 <= realWeightedTerm d i := by
  unfold realWeightedTerm
  have hden : 0 < (2 : ℝ) ^ (i + 1) := by positivity
  exact div_nonneg (mul_nonneg (by positivity) (hd0 (i + 1))) hden.le

theorem realWeightedTerm_le_kernel {d : Nat -> ℝ} (hd1 : forall n, d n <= 1) (i : Nat) :
    realWeightedTerm d i <= realWeightedKernel i := by
  unfold realWeightedTerm realWeightedKernel
  have hden : 0 < (2 : ℝ) ^ (i + 1) := by positivity
  have hnum : 0 <= ((i + 1 : Nat) : ℝ) := by positivity
  calc
    ((i + 1 : Nat) : ℝ) * d (i + 1) / (2 : ℝ) ^ (i + 1)
        <= ((i + 1 : Nat) : ℝ) * 1 / (2 : ℝ) ^ (i + 1) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hd1 (i + 1)) hnum) hden.le
    _ = ((i + 1 : Nat) : ℝ) / (2 : ℝ) ^ (i + 1) := by ring

theorem realWeightedTerm_summable_of_binary {d : Nat -> ℝ} (hd : RealBinaryDigits d) :
    Summable (realWeightedTerm d) := by
  exact Summable.of_norm_bounded realWeightedKernel_summable fun i => by
    rw [Real.norm_of_nonneg (realWeightedTerm_nonneg hd.nonneg i)]
    exact realWeightedTerm_le_kernel hd.le_one i

theorem realWeightedValue_hasSum_of_binary {d : Nat -> ℝ} (hd : RealBinaryDigits d) :
    HasSum (realWeightedTerm d) (realWeightedValue d) := by
  unfold realWeightedValue
  exact (realWeightedTerm_summable_of_binary hd).hasSum

theorem realWeightedPartialSum_mono_of_nonneg {d : Nat -> ℝ}
    (hd0 : forall n, 0 <= d n) {N M : Nat} (hNM : N <= M) :
    realWeightedPartialSum d N <= realWeightedPartialSum d M := by
  have hadd := realWeightedPartialSum_add_tail (d := d) hNM
  have htail : 0 <= realWeightedTail d N M := by
    unfold realWeightedTail realWeightedTerm
    exact Finset.sum_nonneg fun i _ => by
      have hden : 0 < (2 : ℝ) ^ (i + 1) := by positivity
      exact div_nonneg (mul_nonneg (by positivity) (hd0 (i + 1))) hden.le
  linarith

theorem realWeightedPartialSum_le_value_of_binary {d : Nat -> ℝ}
    (hd : RealBinaryDigits d) (N : Nat) :
    realWeightedPartialSum d N <= realWeightedValue d := by
  have hprefix :
      Filter.Tendsto (fun M => realWeightedPartialSum d M) Filter.atTop
        (𝓝 (realWeightedValue d)) := by
    simpa [realWeightedPartialSum] using (realWeightedValue_hasSum_of_binary hd).tendsto_sum_nat
  refine ge_of_tendsto hprefix ?_
  exact Filter.eventually_atTop.2
    ⟨N, fun M hNM => realWeightedPartialSum_mono_of_nonneg hd.nonneg hNM⟩

theorem realWeightedTerm_pos_of_one {d : Nat -> ℝ} {i : Nat} (hd : d (i + 1) = 1) :
    0 < realWeightedTerm d i := by
  unfold realWeightedTerm
  rw [hd]
  positivity

theorem realWeightedPartialSum_lt_of_later_one {d : Nat -> ℝ}
    (hd : RealBinaryDigits d) {N M : Nat} (hNM : N < M) (hone : d M = 1) :
    realWeightedPartialSum d N < realWeightedPartialSum d M := by
  have hMpos : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le N) hNM
  have hpred : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.succ_le_of_lt hMpos)
  have hNpred : N <= M - 1 := by omega
  have hmono := realWeightedPartialSum_mono_of_nonneg hd.nonneg hNpred
  have hsucc := realWeightedPartialSum_succ d (M - 1)
  have hterm : 0 < realWeightedTerm d (M - 1) := by
    apply realWeightedTerm_pos_of_one
    rwa [hpred]
  calc
    realWeightedPartialSum d N <= realWeightedPartialSum d (M - 1) := hmono
    _ < realWeightedPartialSum d (M - 1) + realWeightedTerm d (M - 1) := by linarith
    _ = realWeightedPartialSum d M := by rw [← hsucc, hpred]

theorem realCarry_pos_of_later_one {Q : Nat} {d : Nat -> ℝ} {eta : ℝ} {N M : Nat}
    (hQ : 0 < Q) (hd : RealBinaryDigits d)
    (heta : eta = realWeightedValue d)
    (hNM : N < M) (hone : d M = 1) :
    0 < realCarry Q eta d N := by
  rw [heta]
  unfold realCarry
  have hlt := realWeightedPartialSum_lt_of_later_one hd hNM hone
  have hle := realWeightedPartialSum_le_value_of_binary hd M
  have hdiff : 0 < realWeightedValue d - realWeightedPartialSum d N := by linarith
  positivity

theorem realWeightedTail_nonneg {d : Nat -> ℝ} (hd0 : forall n, 0 <= d n) (N M : Nat) :
    0 <= realWeightedTail d N M := by
  unfold realWeightedTail realWeightedTerm
  exact Finset.sum_nonneg fun i _ => by
    have hden : 0 < (2 : ℝ) ^ (i + 1) := by positivity
    exact div_nonneg (mul_nonneg (by positivity) (hd0 (i + 1))) hden.le

theorem realWeightedTail_le_kernelTail {d : Nat -> ℝ}
    (hd1 : forall n, d n <= 1) (N M : Nat) :
    realWeightedTail d N M <= ∑ i ∈ Finset.Ico N M, realWeightedKernel i := by
  unfold realWeightedTail realWeightedTerm realWeightedKernel
  exact Finset.sum_le_sum fun i _ => by
    have hden : 0 < (2 : ℝ) ^ (i + 1) := by positivity
    have hnum : 0 <= ((i + 1 : Nat) : ℝ) := by positivity
    calc
      ((i + 1 : Nat) : ℝ) * d (i + 1) / (2 : ℝ) ^ (i + 1)
          <= ((i + 1 : Nat) : ℝ) * 1 / (2 : ℝ) ^ (i + 1) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hd1 (i + 1)) hnum) hden.le
      _ = ((i + 1 : Nat) : ℝ) / (2 : ℝ) ^ (i + 1) := by ring

theorem realWeightedTail_le_majorant {d : Nat -> ℝ}
    (hd1 : forall n, d n <= 1) {N M : Nat} (hNM : N <= M) :
    realWeightedTail d N M <= realGeometricTailMajorant N := by
  calc
    realWeightedTail d N M <= ∑ i ∈ Finset.Ico N M, realWeightedKernel i :=
      realWeightedTail_le_kernelTail hd1 N M
    _ = realGeometricTailMajorant N - realGeometricTailMajorant M :=
      realWeightedKernel_sum_Ico_eq hNM
    _ <= realGeometricTailMajorant N := by
      have hM := realGeometricTailMajorant_nonneg M
      linarith

@[simp]
theorem realCarry_zero (Q : Nat) (eta : ℝ) (d : Nat -> ℝ) :
    realCarry Q eta d 0 = (Q : ℝ) * eta := by
  simp [realCarry]

/-- The real carry recurrence (formula (21.1) in `proof_v2.tex`). -/
theorem realCarry_succ (Q : Nat) (eta : ℝ) (d : Nat -> ℝ) (N : Nat) :
    realCarry Q eta d (N + 1) =
      2 * realCarry Q eta d N - (Q : ℝ) * ((N + 1 : Nat) : ℝ) * d (N + 1) := by
  unfold realCarry
  rw [realWeightedPartialSum_succ]
  unfold realWeightedTerm
  field_simp [pow_succ]
  ring

theorem realCarry_finite_target {Q N M : Nat} {d : Nat -> ℝ} (hNM : N <= M) :
    realCarry Q (realWeightedPartialSum d M) d N =
      (Q : ℝ) * (2 : ℝ) ^ N * realWeightedTail d N M := by
  unfold realCarry
  rw [realWeightedPartialSum_sub_eq_tail (d := d) hNM]

theorem realCarry_finite_target_nonneg {Q N M : Nat} {d : Nat -> ℝ}
    (hd0 : forall n, 0 <= d n) (hNM : N <= M) :
    0 <= realCarry Q (realWeightedPartialSum d M) d N := by
  rw [realCarry_finite_target (Q := Q) (d := d) hNM]
  exact mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    (realWeightedTail_nonneg hd0 N M)

theorem realCarry_finite_target_le {Q N M : Nat} {d : Nat -> ℝ}
    (hd1 : forall n, d n <= 1) (hNM : N <= M) :
    realCarry Q (realWeightedPartialSum d M) d N <= (Q : ℝ) * ((N + 2 : Nat) : ℝ) := by
  rw [realCarry_finite_target (Q := Q) (d := d) hNM]
  have htail := realWeightedTail_le_majorant hd1 hNM
  have hfactor : 0 <= (Q : ℝ) * (2 : ℝ) ^ N := by positivity
  calc
    (Q : ℝ) * (2 : ℝ) ^ N * realWeightedTail d N M
        <= (Q : ℝ) * (2 : ℝ) ^ N * realGeometricTailMajorant N := by
          exact mul_le_mul_of_nonneg_left htail hfactor
    _ = (Q : ℝ) * ((N + 2 : Nat) : ℝ) := by
      unfold realGeometricTailMajorant
      field_simp

/--
Finite real analogue of the carry bound (21.2): if the target is a later finite
prefix of a binary digit sequence, then the carry at an earlier prefix is between
`0` and `Q (N+2)`.
-/
theorem realCarry_finite_target_bounds_of_binary {Q N M : Nat} {d : Nat -> ℝ}
    (hd : RealBinaryDigits d) (hNM : N <= M) :
    0 <= realCarry Q (realWeightedPartialSum d M) d N /\
      realCarry Q (realWeightedPartialSum d M) d N <= (Q : ℝ) * ((N + 2 : Nat) : ℝ) :=
  ⟨realCarry_finite_target_nonneg hd.nonneg hNM,
    realCarry_finite_target_le hd.le_one hNM⟩

/--
Infinite real carry bound: when `eta` is the sum of the weighted binary series,
the carry at every finite prefix is bounded between `0` and `Q (N+2)`.
-/
theorem realCarry_bounds_of_hasSum {Q N : Nat} {d : Nat -> ℝ} {eta : ℝ}
    (hd : RealBinaryDigits d)
    (heta : HasSum (realWeightedTerm d) eta) :
    0 <= realCarry Q eta d N /\
      realCarry Q eta d N <= (Q : ℝ) * ((N + 2 : Nat) : ℝ) := by
  have hprefix :
      Filter.Tendsto (fun M => realWeightedPartialSum d M) Filter.atTop (𝓝 eta) := by
    simpa [realWeightedPartialSum] using heta.tendsto_sum_nat
  have hcarry :
      Filter.Tendsto (fun M => realCarry Q (realWeightedPartialSum d M) d N)
        Filter.atTop (𝓝 (realCarry Q eta d N)) := by
    simpa [realCarry] using
      (hprefix.sub tendsto_const_nhds).const_mul ((Q : ℝ) * (2 : ℝ) ^ N)
  refine ⟨?_, ?_⟩
  · refine ge_of_tendsto hcarry ?_
    exact Filter.eventually_atTop.2
      ⟨N, fun M hNM => realCarry_finite_target_nonneg (Q := Q) (d := d) hd.nonneg hNM⟩
  · refine le_of_tendsto hcarry ?_
    exact Filter.eventually_atTop.2
      ⟨N, fun M hNM => realCarry_finite_target_le (Q := Q) (d := d) hd.le_one hNM⟩

/--
Unconditional infinite carry bound for the `tsum` value attached to a binary
digit sequence.
-/
theorem realCarry_bounds_of_binary_tsum {Q N : Nat} {d : Nat -> ℝ}
    (hd : RealBinaryDigits d) :
    0 <= realCarry Q (realWeightedValue d) d N /\
      realCarry Q (realWeightedValue d) d N <= (Q : ℝ) * ((N + 2 : Nat) : ℝ) :=
  realCarry_bounds_of_hasSum hd (realWeightedValue_hasSum_of_binary hd)

end

end Erdos260
