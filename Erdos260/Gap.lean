import Mathlib
import Erdos260.IntegerCarry

/-!
# Zero-gap dyadic bounds

This file packages the carry-growth lemma into dyadic exponent estimates.  The
results are still local: later proof files must provide the scale hypotheses
that place a zero gap inside a dyadic region.
-/

namespace Erdos260

noncomputable section

open scoped Topology

/-- Natural-number form of the zero-gap carry growth bound. -/
theorem nat_pow_two_le_of_zero_gap {Q : Nat} {P : Int} {d : Nat -> Nat} {N h : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hRpos : 0 < integerCarry Q P d N)
    (hzero : ∀ j : Nat, N < j -> j <= N + h -> d j = 0) :
    2 ^ h <= Q * (N + h + 2) := by
  have hInt := pow_two_le_of_zero_gap (Q := Q) (P := P) (d := d) (N := N) (h := h)
    hQ hd heta hRpos hzero
  exact_mod_cast hInt

theorem exponent_le_of_pow_two_le_pow_two {h L : Nat}
    (hle : 2 ^ h <= 2 ^ L) :
    h <= L := by
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hle

theorem exponent_le_of_pow_two_le_mul_dyadic {h L B A : Nat}
    (hpow : 2 ^ h <= A * 2 ^ L) (hA : A <= 2 ^ B) :
    h <= L + B := by
  have hmul : A * 2 ^ L <= 2 ^ B * 2 ^ L := by
    exact Nat.mul_le_mul_right _ hA
  have hp : 2 ^ h <= 2 ^ (L + B) := by
    calc
      2 ^ h <= A * 2 ^ L := hpow
      _ <= 2 ^ B * 2 ^ L := hmul
      _ = 2 ^ (L + B) := by rw [pow_add, Nat.mul_comm]
  exact exponent_le_of_pow_two_le_pow_two hp

/--
Zero-gap length bound once the later endpoint is known to lie below a dyadic
scale and the constant factor is absorbed into `2^B`.
-/
theorem zero_gap_len_le_dyadic_scale {Q C B X L : Nat} {P : Int} {d : Nat -> Nat} {N h : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hRpos : 0 < integerCarry Q P d N)
    (hzero : ∀ j : Nat, N < j -> j <= N + h -> d j = 0)
    (hX : X = 2 ^ L)
    (hscale : N + h + 2 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    h <= L + B := by
  have hnat := nat_pow_two_le_of_zero_gap (Q := Q) (P := P) (d := d) (N := N) (h := h)
    hQ hd heta hRpos hzero
  have hpow : 2 ^ h <= (Q * C) * 2 ^ L := by
    calc
      2 ^ h <= Q * (N + h + 2) := hnat
      _ <= Q * (C * X) := Nat.mul_le_mul_left Q hscale
      _ = (Q * C) * 2 ^ L := by rw [hX]; ring
  exact exponent_le_of_pow_two_le_mul_dyadic (h := h) (L := L) (B := B) (A := Q * C) hpow hconst

theorem zero_gap_len_le_of_dyadic_scale {Q C B X : Nat} {P : Int} {d : Nat -> Nat} {N h : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hRpos : 0 < integerCarry Q P d N)
    (hzero : ∀ j : Nat, N < j -> j <= N + h -> d j = 0)
    (hX : Dyadic X)
    (hscale : N + h + 2 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    ∃ L : Nat, X = 2 ^ L ∧ h <= L + B := by
  rcases hX with ⟨L, hL⟩
  exact ⟨L, hL, zero_gap_len_le_dyadic_scale hQ hd heta hRpos hzero hL hscale hconst⟩

end

end Erdos260
