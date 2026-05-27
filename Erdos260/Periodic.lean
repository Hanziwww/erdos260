import Mathlib
import Erdos260.Support

/-!
# Finite periodic-word arithmetic

This file records elementary finite-period arithmetic used around Lemma 24.2:
binary masks, their weights, the denominator `2^p - 1`, and the denominator
drop `D ∣ A*M -> D/gcd(D,A) ∣ M`.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Little-endian binary mask of a period word of length `p`. -/
def periodMask (d : Nat -> Nat) (p : Nat) : Nat :=
  ∑ j ∈ range p, d j * 2 ^ j

/-- Number of ones in a period word of length `p`. -/
def periodWeight (d : Nat -> Nat) (p : Nat) : Nat :=
  ∑ j ∈ range p, d j

/-- Denominator of a purely periodic binary word of period `p`. -/
def periodDen (p : Nat) : Nat :=
  2 ^ p - 1

theorem sum_range_two_pow_eq_periodDen (p : Nat) :
    (∑ j ∈ range p, 2 ^ j) = periodDen p := by
  unfold periodDen
  induction p with
  | zero => simp
  | succ p ih =>
      rw [sum_range_succ, ih]
      have hpow : 1 <= 2 ^ p := Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : 0 < 2))
      omega

theorem periodDen_pos {p : Nat} (hp : 0 < p) :
    0 < periodDen p := by
  unfold periodDen
  have h : 1 < 2 ^ p := Nat.one_lt_pow hp.ne' (by norm_num)
  omega

theorem periodMask_le_periodDen {d : Nat -> Nat} (hd : BinaryDigits d) (p : Nat) :
    periodMask d p <= periodDen p := by
  have hsum : periodMask d p <= ∑ j ∈ range p, 2 ^ j := by
    unfold periodMask
    exact sum_le_sum fun j _ => by
      rcases hd j with h | h <;> simp [h]
  rwa [sum_range_two_pow_eq_periodDen] at hsum

theorem periodWeight_le_length {d : Nat -> Nat} (hd : BinaryDigits d) (p : Nat) :
    periodWeight d p <= p := by
  unfold periodWeight
  calc
    (∑ j ∈ range p, d j) <= ∑ j ∈ range p, 1 := by
      exact sum_le_sum fun j _ => by
        rcases hd j with h | h <;> simp [h]
    _ = p := by simp

theorem periodDensity_nat_bound {d : Nat -> Nat} (hd : BinaryDigits d) (p : Nat) :
    periodWeight d p <= p :=
  periodWeight_le_length hd p

theorem periodMask_eq_zero_of_zero {d : Nat -> Nat} {p : Nat}
    (hzero : ∀ j : Nat, j < p -> d j = 0) :
    periodMask d p = 0 := by
  unfold periodMask
  exact sum_eq_zero fun j hj => by
    rw [mem_range] at hj
    simp [hzero j hj]

theorem periodWeight_eq_zero_of_zero {d : Nat -> Nat} {p : Nat}
    (hzero : ∀ j : Nat, j < p -> d j = 0) :
    periodWeight d p = 0 := by
  unfold periodWeight
  exact sum_eq_zero fun j hj => by
    rw [mem_range] at hj
    exact hzero j hj

theorem periodWeight_pos_of_exists_one {d : Nat -> Nat} {p : Nat}
    (hone : ∃ j : Nat, j < p ∧ d j = 1) :
    0 < periodWeight d p := by
  rcases hone with ⟨j, hj, hdj⟩
  unfold periodWeight
  have hmem : j ∈ range p := by simpa using hj
  calc
    0 < d j := by simp [hdj]
    _ <= ∑ k ∈ range p, d k := by
          exact single_le_sum (fun _ _ => Nat.zero_le _) hmem

theorem periodMask_pos_of_exists_one {d : Nat -> Nat} {p : Nat}
    (hone : ∃ j : Nat, j < p ∧ d j = 1) :
    0 < periodMask d p := by
  rcases hone with ⟨j, hj, hdj⟩
  unfold periodMask
  have hmem : j ∈ range p := by simpa using hj
  calc
    0 < d j * 2 ^ j := by
          simp [hdj, Nat.pow_pos (by norm_num : 0 < 2)]
    _ <= ∑ k ∈ range p, d k * 2 ^ k := by
          exact single_le_sum
            (s := range p) (f := fun k => d k * 2 ^ k)
            (fun _ _ => Nat.zero_le _) hmem

theorem all_zero_of_periodWeight_eq_zero {d : Nat -> Nat} {p : Nat}
    (hweight : periodWeight d p = 0) :
    ∀ j : Nat, j < p -> d j = 0 := by
  intro j hj
  by_contra hne
  have hpos : 0 < d j := Nat.pos_of_ne_zero hne
  unfold periodWeight at hweight
  have hmem : j ∈ range p := by simpa using hj
  have hle : d j <= ∑ k ∈ range p, d k :=
    single_le_sum (fun _ _ => Nat.zero_le _) hmem
  omega

theorem all_zero_of_periodMask_eq_zero {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hmask : periodMask d p = 0) :
    ∀ j : Nat, j < p -> d j = 0 := by
  intro j hj
  rcases hd j with hzero | hone
  · exact hzero
  · have hpos := periodMask_pos_of_exists_one
      (d := d) (p := p) ⟨j, hj, hone⟩
    omega

theorem exists_one_of_periodWeight_pos {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hpos : 0 < periodWeight d p) :
    ∃ j : Nat, j < p ∧ d j = 1 := by
  by_contra hnone
  have hzero : ∀ j : Nat, j < p -> d j = 0 := by
    intro j hj
    rcases hd j with hdj | hdj
    · exact hdj
    · exact False.elim (hnone ⟨j, hj, hdj⟩)
  have hweight_zero := periodWeight_eq_zero_of_zero hzero
  omega

theorem periodMask_eq_periodDen_of_one {d : Nat -> Nat} {p : Nat}
    (hone : ∀ j : Nat, j < p -> d j = 1) :
    periodMask d p = periodDen p := by
  unfold periodMask
  rw [← sum_range_two_pow_eq_periodDen p]
  exact sum_congr rfl fun j hj => by
    rw [mem_range] at hj
    simp [hone j hj]

theorem periodWeight_eq_length_of_one {d : Nat -> Nat} {p : Nat}
    (hone : ∀ j : Nat, j < p -> d j = 1) :
    periodWeight d p = p := by
  unfold periodWeight
  calc
    (∑ j ∈ range p, d j) = ∑ j ∈ range p, 1 := by
      exact sum_congr rfl fun j hj => by
        rw [mem_range] at hj
        simp [hone j hj]
    _ = p := by simp

theorem periodWeight_lt_length_of_exists_zero {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hzero : ∃ j : Nat, j < p ∧ d j = 0) :
    periodWeight d p < p := by
  rcases hzero with ⟨j, hj, hdj⟩
  unfold periodWeight
  have hmem : j ∈ range p := by simpa using hj
  have hdecomp :
      (∑ k ∈ range p, d k) =
        d j + ∑ k ∈ (range p).erase j, d k := by
    exact (Finset.add_sum_erase (s := range p) (f := d) hmem).symm
  have herase_le :
      (∑ k ∈ (range p).erase j, d k) <= ((range p).erase j).card := by
    calc
      (∑ k ∈ (range p).erase j, d k) <=
          ∑ _k ∈ (range p).erase j, 1 := by
            exact sum_le_sum fun k _ => by
              rcases hd k with h | h <;> simp [h]
      _ = ((range p).erase j).card := by simp
  have hcard : ((range p).erase j).card = p - 1 := by
    simp [hmem]
  rw [hdecomp, hdj]
  omega

theorem periodMask_lt_periodDen_of_exists_zero {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hzero : ∃ j : Nat, j < p ∧ d j = 0) :
    periodMask d p < periodDen p := by
  rcases hzero with ⟨j, hj, hdj⟩
  unfold periodMask
  rw [← sum_range_two_pow_eq_periodDen p]
  have hmem : j ∈ range p := by simpa using hj
  have hmask_decomp :
      (∑ k ∈ range p, d k * 2 ^ k) =
        d j * 2 ^ j + ∑ k ∈ (range p).erase j, d k * 2 ^ k := by
    exact (Finset.add_sum_erase
      (s := range p) (f := fun k => d k * 2 ^ k) hmem).symm
  have hfull_decomp :
      (∑ k ∈ range p, 2 ^ k) =
        2 ^ j + ∑ k ∈ (range p).erase j, 2 ^ k := by
    exact (Finset.add_sum_erase
      (s := range p) (f := fun k => 2 ^ k) hmem).symm
  have herase_le :
      (∑ k ∈ (range p).erase j, d k * 2 ^ k) <=
        ∑ k ∈ (range p).erase j, 2 ^ k := by
    exact sum_le_sum fun k _ => by
      rcases hd k with h | h <;> simp [h]
  rw [hmask_decomp, hfull_decomp, hdj]
  have hpowpos : 0 < 2 ^ j := Nat.pow_pos (by norm_num : 0 < 2)
  omega

theorem all_one_of_periodWeight_eq_length {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hweight : periodWeight d p = p) :
    ∀ j : Nat, j < p -> d j = 1 := by
  intro j hj
  rcases hd j with hzero | hone
  · have hlt := periodWeight_lt_length_of_exists_zero
      (d := d) (p := p) hd ⟨j, hj, hzero⟩
    omega
  · exact hone

theorem all_one_of_periodMask_eq_periodDen {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hmask : periodMask d p = periodDen p) :
    ∀ j : Nat, j < p -> d j = 1 := by
  intro j hj
  rcases hd j with hzero | hone
  · have hlt := periodMask_lt_periodDen_of_exists_zero
      (d := d) (p := p) hd ⟨j, hj, hzero⟩
    omega
  · exact hone

theorem div_gcd_dvd_of_dvd_mul {D A M : Nat} (hD : 0 < D) (h : D ∣ A * M) :
    D / D.gcd A ∣ M := by
  have hmod0 : A * M ≡ 0 [MOD D] := (Nat.modEq_zero_iff_dvd).2 h
  have hmod : A * M ≡ A * 0 [MOD D] := by simpa using hmod0
  have hcancel := hmod.cancel_left_div_gcd hD
  simpa using (Nat.modEq_zero_iff_dvd).1 hcancel

theorem period_den_div_gcd_dvd_mask_of_dvd {p A M : Nat}
    (hp : 0 < p) (h : periodDen p ∣ A * M) :
    periodDen p / (periodDen p).gcd A ∣ M :=
  div_gcd_dvd_of_dvd_mul (periodDen_pos hp) h

theorem period_den_gcd_le_factor {p A : Nat} (hA : 0 < A) :
    (periodDen p).gcd A <= A :=
  Nat.gcd_le_right (periodDen p) hA

theorem period_den_drop_dvd_mask_of_dvd_Qp {Q p M : Nat}
    (hp : 0 < p) (h : periodDen p ∣ (Q * p) * M) :
    periodDen p / (periodDen p).gcd (Q * p) ∣ M :=
  period_den_div_gcd_dvd_mask_of_dvd hp h

theorem period_den_gcd_Qp_le {Q p : Nat} (hQ : 0 < Q) (hp : 0 < p) :
    (periodDen p).gcd (Q * p) <= Q * p :=
  period_den_gcd_le_factor (Nat.mul_pos hQ hp)

end

end Erdos260
