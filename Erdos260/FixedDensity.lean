import Erdos260.BinaryOrbit
import Erdos260.Periodic
import Erdos260.RationalSeparation

/-!
# Fixed-density periodic repetition primitives

This file packages the already-proved finite orbit, denominator-drop, and
rational-separation lemmas into the local shapes used by Lemma 24.2 and
Proposition 24.3 of `proof_v2.tex`.
-/

namespace Erdos260

noncomputable section

/-- Real density of ones in a period word. -/
def periodDensity (d : Nat -> Nat) (p : Nat) : ℝ :=
  (periodWeight d p : ℝ) / (p : ℝ)

theorem periodDensity_nonneg (d : Nat -> Nat) (p : Nat) :
    0 <= periodDensity d p := by
  unfold periodDensity
  positivity

theorem periodDensity_le_one {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hp : 0 < p) :
    periodDensity d p <= 1 := by
  unfold periodDensity
  have hpℝ : 0 < (p : ℝ) := by exact_mod_cast hp
  have hleℝ : (periodWeight d p : ℝ) <= (p : ℝ) := by
    exact_mod_cast periodWeight_le_length hd p
  exact (div_le_iff₀ hpℝ).2 (by simpa using hleℝ)

theorem periodDensity_eq_zero_of_periodWeight_eq_zero {d : Nat -> Nat} {p : Nat}
    (h : periodWeight d p = 0) :
    periodDensity d p = 0 := by
  simp [periodDensity, h]

theorem periodDensity_eq_zero_of_zero {d : Nat -> Nat} {p : Nat}
    (hzero : ∀ j : Nat, j < p -> d j = 0) :
    periodDensity d p = 0 :=
  periodDensity_eq_zero_of_periodWeight_eq_zero
    (periodWeight_eq_zero_of_zero hzero)

theorem periodDensity_pos_of_periodWeight_pos {d : Nat -> Nat} {p : Nat}
    (hp : 0 < p) (hpos : 0 < periodWeight d p) :
    0 < periodDensity d p := by
  unfold periodDensity
  have hpℝ : 0 < (p : ℝ) := by exact_mod_cast hp
  have hwℝ : 0 < (periodWeight d p : ℝ) := by exact_mod_cast hpos
  exact div_pos hwℝ hpℝ

theorem periodDensity_pos_of_exists_one {d : Nat -> Nat} {p : Nat}
    (hp : 0 < p) (hone : ∃ j : Nat, j < p ∧ d j = 1) :
    0 < periodDensity d p :=
  periodDensity_pos_of_periodWeight_pos hp
    (periodWeight_pos_of_exists_one hone)

theorem periodDensity_lt_one_of_periodWeight_lt_length {d : Nat -> Nat} {p : Nat}
    (hp : 0 < p) (hlt : periodWeight d p < p) :
    periodDensity d p < 1 := by
  unfold periodDensity
  have hpℝ : 0 < (p : ℝ) := by exact_mod_cast hp
  have hltℝ : (periodWeight d p : ℝ) < (p : ℝ) := by exact_mod_cast hlt
  exact (div_lt_iff₀ hpℝ).2 (by simpa using hltℝ)

theorem periodDensity_lt_one_of_exists_zero {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hp : 0 < p)
    (hzero : ∃ j : Nat, j < p ∧ d j = 0) :
    periodDensity d p < 1 :=
  periodDensity_lt_one_of_periodWeight_lt_length hp
    (periodWeight_lt_length_of_exists_zero hd hzero)

theorem exactPeriodicCompletion_density_lower_from_orbit
    {Q p k : Nat} (hQ : 0 < Q) (hp : 0 < p)
    (horbit : p + 1 <= 2 * Q * k) :
    (1 : ℝ) / ((3 * Q : Nat) : ℝ) <= (k : ℝ) / (p : ℝ) :=
  orbit_digit_density_real_lower_third hQ hp horbit

theorem exactPeriodicCompletion_periodWeight_density_lower_from_orbit
    {Q p : Nat} {d : Nat -> Nat} (hQ : 0 < Q) (hp : 0 < p)
    (horbit : p + 1 <= 2 * Q * periodWeight d p) :
    (1 : ℝ) / ((3 * Q : Nat) : ℝ) <= periodDensity d p := by
  unfold periodDensity
  exact exactPeriodicCompletion_density_lower_from_orbit hQ hp horbit

theorem exactPeriodicCompletion_denominator_drop {Q p : Nat} {d : Nat -> Nat}
    (hp : 0 < p)
    (hdiv : periodDen p ∣ (Q * p) * periodMask d p) :
    periodDen p / (periodDen p).gcd (Q * p) ∣ periodMask d p :=
  period_den_drop_dvd_mask_of_dvd_Qp hp hdiv

theorem exactPeriodicCompletion_gcd_bound {Q p : Nat}
    (hQ : 0 < Q) (hp : 0 < p) :
    (periodDen p).gcd (Q * p) <= Q * p :=
  period_den_gcd_Qp_le hQ hp

theorem fixedDensity_rationalSeparation_forces_eq
    {P A : Int} {Q B : Nat} (hQ : 0 < Q) (hB : 0 < B)
    (hlt :
      |(P : ℝ) / (Q : ℝ) - (A : ℝ) / (B : ℝ)| <
        (1 : ℝ) / ((Q : ℝ) * (B : ℝ))) :
    (P : ℝ) / (Q : ℝ) = (A : ℝ) / (B : ℝ) :=
  rat_div_eq_of_abs_sub_lt_inv_mul hQ hB hlt

end

end Erdos260
