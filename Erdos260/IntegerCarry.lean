import Mathlib
import Erdos260.Density

/-!
# Integer carry for rational targets

For a rational target `P / Q`, the real carry from `proof_v2.tex` is an integer
sequence satisfying the exact recurrence
`R_{N+1} = 2 R_N - Q (N+1) d_{N+1}`.  This file defines that integer sequence
recursively and proves that its real cast agrees with `realCarry`.
-/

namespace Erdos260

noncomputable section

open scoped Topology

/-- Integer carry for the rational target `P / Q`. -/
def integerCarry (Q : Nat) (P : Int) (d : Nat -> Nat) : Nat -> Int
  | 0 => P
  | N + 1 => 2 * integerCarry Q P d N - (Q : Int) * ((N + 1 : Nat) : Int) * (d (N + 1) : Int)

@[simp]
theorem integerCarry_zero (Q : Nat) (P : Int) (d : Nat -> Nat) :
    integerCarry Q P d 0 = P := rfl

@[simp]
theorem integerCarry_succ (Q : Nat) (P : Int) (d : Nat -> Nat) (N : Nat) :
    integerCarry Q P d (N + 1) =
      2 * integerCarry Q P d N - (Q : Int) * ((N + 1 : Nat) : Int) * (d (N + 1) : Int) := rfl

/-- The recursively defined integer carry agrees with the real carry. -/
theorem integerCarry_cast_real {Q : Nat} (hQ : 0 < Q) (P : Int) (d : Nat -> Nat) (N : Nat) :
    ((integerCarry Q P d N : Int) : ℝ) =
      realCarry Q ((P : ℝ) / (Q : ℝ)) (natBinaryAsReal d) N := by
  induction N with
  | zero =>
      have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
      simp [integerCarry, realCarry]
      field_simp [hQne]
  | succ N ih =>
      rw [integerCarry_succ, realCarry_succ, ← ih]
      simp [natBinaryAsReal]

/-- Integer version of the carry bound for a rational weighted binary value. -/
theorem integerCarry_bounds_of_rational_value {Q : Nat} {P : Int} {d : Nat -> Nat} (N : Nat)
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    0 <= integerCarry Q P d N ∧ integerCarry Q P d N <= (Q : Int) * ((N + 2 : Nat) : Int) := by
  have hreal := realCarry_bounds_of_binary_tsum (Q := Q) (N := N) (d := natBinaryAsReal d)
    (natBinaryAsReal_digits hd)
  rw [heta] at hreal
  have hcast := integerCarry_cast_real (Q := Q) hQ P d N
  rw [← hcast] at hreal
  constructor
  · exact_mod_cast hreal.1
  · exact_mod_cast hreal.2

theorem integerCarry_succ_of_zero (Q : Nat) (P : Int) (d : Nat -> Nat) {N : Nat}
    (hzero : d (N + 1) = 0) :
    integerCarry Q P d (N + 1) = 2 * integerCarry Q P d N := by
  rw [integerCarry_succ, hzero]
  ring

theorem integerCarry_succ_of_one (Q : Nat) (P : Int) (d : Nat -> Nat) {N : Nat}
    (hone : d (N + 1) = 1) :
    integerCarry Q P d (N + 1) =
      2 * integerCarry Q P d N - (Q : Int) * ((N + 1 : Nat) : Int) := by
  rw [integerCarry_succ, hone]
  norm_num

/-- If a block has only zero digits after `N`, the carry doubles across the block. -/
theorem integerCarry_add_of_zero_digits (Q : Nat) (P : Int) (d : Nat -> Nat) (N h : Nat)
    (hzero : ∀ j : Nat, N < j -> j <= N + h -> d j = 0) :
    integerCarry Q P d (N + h) = (2 : Int) ^ h * integerCarry Q P d N := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hzero_prev : ∀ j : Nat, N < j -> j <= N + h -> d j = 0 := by
        intro j hj1 hj2
        exact hzero j hj1 (by omega)
      have hlast : d (N + h + 1) = 0 := by
        exact hzero (N + h + 1) (by omega) (by omega)
      calc
        integerCarry Q P d (N + (h + 1)) = integerCarry Q P d ((N + h) + 1) := by
          exact congrArg (integerCarry Q P d) (by omega)
        _ = 2 * integerCarry Q P d (N + h) := by
          exact integerCarry_succ_of_zero Q P d hlast
        _ = 2 * ((2 : Int) ^ h * integerCarry Q P d N) := by rw [ih hzero_prev]
        _ = (2 : Int) ^ (h + 1) * integerCarry Q P d N := by
          rw [pow_succ]
          ring

theorem integerCarry_succ_modEq_step (Q : Nat) (P : Int) (d : Nat -> Nat) (N : Nat) :
    integerCarry Q P d (N + 1) ≡ 2 * integerCarry Q P d N
      [ZMOD (Q : Int) * ((N + 1 : Nat) : Int)] := by
  rw [Int.modEq_iff_dvd]
  rw [integerCarry_succ]
  refine ⟨(d (N + 1) : Int), ?_⟩
  ring

theorem integerCarry_succ_modEq_Q (Q : Nat) (P : Int) (d : Nat -> Nat) (N : Nat) :
    integerCarry Q P d (N + 1) ≡ 2 * integerCarry Q P d N [ZMOD (Q : Int)] := by
  rw [Int.modEq_iff_dvd]
  rw [integerCarry_succ]
  refine ⟨((N + 1 : Nat) : Int) * (d (N + 1) : Int), ?_⟩
  ring

theorem integerCarry_pos_of_later_one {Q : Nat} {P : Int} {d : Nat -> Nat} {N M : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hNM : N < M) (hone : d M = 1) :
    0 < integerCarry Q P d N := by
  have hreal : 0 < realCarry Q ((P : ℝ) / (Q : ℝ)) (natBinaryAsReal d) N := by
    apply realCarry_pos_of_later_one (Q := Q) (d := natBinaryAsReal d)
        (eta := (P : ℝ) / (Q : ℝ))
    · exact hQ
    · exact natBinaryAsReal_digits hd
    · exact heta.symm
    · exact hNM
    · simp [natBinaryAsReal, hone]
  have hcast := integerCarry_cast_real (Q := Q) hQ P d N
  rw [← hcast] at hreal
  exact_mod_cast hreal

/--
Quantitative zero-gap growth: if the carry at `N` is positive and all digits in
`(N, N+h]` are zero, then the upper carry bound forces `2^h` below the later
linear carry envelope.
-/
theorem pow_two_le_of_zero_gap {Q : Nat} {P : Int} {d : Nat -> Nat} {N h : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hRpos : 0 < integerCarry Q P d N)
    (hzero : ∀ j : Nat, N < j -> j <= N + h -> d j = 0) :
    (2 : Int) ^ h <= (Q : Int) * (((N + h) + 2 : Nat) : Int) := by
  have hbounds :=
    integerCarry_bounds_of_rational_value (Q := Q) (P := P) (d := d) (N + h) hQ hd heta
  have hrun := integerCarry_add_of_zero_digits Q P d N h hzero
  have hupper :
      (2 : Int) ^ h * integerCarry Q P d N <=
        (Q : Int) * (((N + h) + 2 : Nat) : Int) := by
    simpa [hrun] using hbounds.2
  have hRge : (1 : Int) <= integerCarry Q P d N := by omega
  have hpow_nonneg : 0 <= (2 : Int) ^ h := by positivity
  have hle_mul : (2 : Int) ^ h <= (2 : Int) ^ h * integerCarry Q P d N := by
    calc
      (2 : Int) ^ h = (2 : Int) ^ h * 1 := by ring
      _ <= (2 : Int) ^ h * integerCarry Q P d N :=
        mul_le_mul_of_nonneg_left hRge hpow_nonneg
  exact hle_mul.trans hupper

end

end Erdos260
