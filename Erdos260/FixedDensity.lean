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

open Finset

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

/-!
## Lemma 24.2 (exact periodic completion has positive density)

For a primitive period word `w` of length `p` (`hper` says `w` has period `p`,
`hprim` says no smaller positive period), with mask `M = periodMask d p` and
denominator `D = periodDen p = 2^p - 1`, suppose the periodic completion is the
rational `P/Q`.  Clearing denominators (`hdiv`) gives `D ∣ Q·p·M`, the
manuscript's denominator-drop hypothesis.  Then the density of ones satisfies
`wt(w)/p ≥ 1/(3Q)`.

The proof reduces `M/D` to lowest terms `a/q` with `q` odd and `q ≤ Q·p`,
excludes `q = 1` (which forces a constant — hence period-`1` — word), shows the
binary orbit `2^j M % D` has exactly `p` distinct positive residues
(`ord_q(2) = p`, forced by primitivity), and applies Lemma 24.1.
-/
theorem fixedDensity_exact_completion_lower
    {d : Nat -> Nat} {p Q : Nat}
    (hp : 2 <= p)
    (hQ : 0 < Q)
    (hd : BinaryDigits d)
    (hper : ∀ j, d (j + p) = d j)
    (hprim : ∀ s, 0 < s -> s < p -> ∃ k, d (k + s) ≠ d k)
    (hdiv : periodDen p ∣ (Q * p) * periodMask d p) :
    (1 : ℝ) / ((3 * Q : Nat) : ℝ) <= periodDensity d p := by
  have hp0 : 0 < p := by omega
  set M := periodMask d p with hMdef
  set D := periodDen p with hDdef
  have hDpos : 0 < D := periodDen_pos hp0
  have hMleD : M <= D := periodMask_le_periodDen hd p
  -- a constant word would have period 1, contradicting primitivity
  have key_const : ∀ c : Nat, (∀ j, j < p -> d j = c) -> False := by
    intro c hc
    have hall : ∀ n, d n = c := by
      intro n
      have hn := digit_add_mul_period hper (n / p) (n % p)
      rw [Nat.mod_add_div' n p] at hn
      rw [hn]
      exact hc (n % p) (Nat.mod_lt _ hp0)
    obtain ⟨k, hk⟩ := hprim 1 (by norm_num) (by omega)
    exact hk (by rw [hall (k + 1), hall k])
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · exact absurd (all_zero_of_periodMask_eq_zero hd hM0) (key_const 0)
    · exact hM0
  have hMltD : M < D := by
    rcases lt_or_eq_of_le hMleD with h | h
    · exact h
    · exact absurd (all_one_of_periodMask_eq_periodDen hd h) (key_const 1)
  -- reduced denominator q = D / gcd(M, D)
  set g := Nat.gcd M D with hgdef
  have hg_pos : 0 < g := Nat.gcd_pos_iff.mpr (Or.inr hDpos)
  have hg_dvd_M : g ∣ M := Nat.gcd_dvd_left M D
  have hg_dvd_D : g ∣ D := Nat.gcd_dvd_right M D
  set q := D / g with hqdef
  set a := M / g with hadef
  have hDgq : D = g * q := (Nat.mul_div_cancel' hg_dvd_D).symm
  have hMga : M = g * a := (Nat.mul_div_cancel' hg_dvd_M).symm
  have hq_dvd_D : q ∣ D := ⟨g, by rw [hDgq]; ring⟩
  have hcop_qa : Nat.Coprime q a := (Nat.coprime_div_gcd_div_gcd hg_pos).symm
  have hgleM : g <= M := Nat.le_of_dvd hMpos hg_dvd_M
  have hgltD : g < D := lt_of_le_of_lt hgleM hMltD
  have hq2 : 2 <= q := by
    rcases Nat.lt_or_ge q 2 with hq | hq
    · exfalso
      have hle : D <= g := by
        calc D = g * q := hDgq
          _ <= g * 1 := Nat.mul_le_mul (le_refl g) (by omega)
          _ = g := Nat.mul_one g
      omega
    · exact hq
  -- q is odd, since it divides the odd number D = 2^p - 1
  have hDodd : D % 2 = 1 := by
    have h0 : (2 : ℕ) ^ p % 2 = 0 := by
      rcases dvd_pow_self 2 hp0.ne' with ⟨m, hm⟩
      omega
    have hge : 2 <= (2 : ℕ) ^ p := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ <= 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp0
    have hDval : D = 2 ^ p - 1 := hDdef
    omega
  have hnot2q : ¬ (2 ∣ q) := by
    intro h2q
    have h2D : (2 : ℕ) ∣ D := dvd_trans h2q hq_dvd_D
    rcases h2D with ⟨k, hk⟩
    omega
  have hcop_q2 : Nat.Coprime q 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2q).symm
  -- q ≤ Q·p from the denominator drop
  have hq_dvd_Qp : q ∣ Q * p := by
    have hh : g * q ∣ g * ((Q * p) * a) := by
      have hd2 : D ∣ (Q * p) * M := hdiv
      rw [hDgq, show (Q * p) * M = g * ((Q * p) * a) from by rw [hMga]; ring] at hd2
      exact hd2
    have hq1 : q ∣ (Q * p) * a := (mul_dvd_mul_iff_left hg_pos.ne').1 hh
    exact hcop_qa.dvd_of_dvd_mul_right hq1
  have hq_le : q <= Q * p := Nat.le_of_dvd (Nat.mul_pos hQ hp0) hq_dvd_Qp
  -- the binary orbit O j = 2^j M % D is divisible by g and strictly positive
  have hg_dvd_O : ∀ j, g ∣ (2 ^ j * M) % D :=
    fun j => (Nat.dvd_mod_iff hg_dvd_D).2 (hg_dvd_M.mul_left (2 ^ j))
  have hOpos : ∀ j, 0 < (2 ^ j * M) % D := by
    intro j
    rcases Nat.eq_zero_or_pos ((2 ^ j * M) % D) with h0 | h0
    · exfalso
      have hdvd : D ∣ 2 ^ j * M := Nat.dvd_of_mod_eq_zero h0
      rw [hDgq, hMga, show 2 ^ j * (g * a) = g * (2 ^ j * a) from by ring] at hdvd
      have hq1 : q ∣ 2 ^ j * a := (mul_dvd_mul_iff_left hg_pos.ne').1 hdvd
      have hcop : Nat.Coprime q (2 ^ j * a) :=
        Nat.Coprime.mul_right (hcop_q2.pow_right j) hcop_qa
      have hgcd : Nat.gcd q (2 ^ j * a) = q := Nat.gcd_eq_left hq1
      have hcopeq : Nat.gcd q (2 ^ j * a) = 1 := hcop
      omega
    · exact h0
  -- distinct residues: a coincidence would force a sub-period of w
  have orbit_inj : ∀ x y, x < p -> y < p ->
      (2 ^ x * M) % D = (2 ^ y * M) % D -> x = y := by
    intro x y hx hy hxy
    rcases lt_trichotomy x y with h | h | h
    · exfalso
      have hcyc := digit_cyclic_of_orbit_eq hp0 hd hMltD h hy hxy
      have hglob := digit_periodic_of_cyclic hp0 hper hcyc
      obtain ⟨k, hk⟩ := hprim (y - x) (by omega) (by omega)
      exact hk (hglob k)
    · exact h
    · exfalso
      have hcyc := digit_cyclic_of_orbit_eq hp0 hd hMltD h hx hxy.symm
      have hglob := digit_periodic_of_cyclic hp0 hper hcyc
      obtain ⟨k, hk⟩ := hprim (x - y) (by omega) (by omega)
      exact hk (hglob k)
  -- the residue set has p distinct positive elements
  have hrinj_on : Set.InjOn (fun j => (2 ^ j * M) % D / g) (range p) := by
    intro x hx y hy hxy
    simp only [coe_range, Set.mem_Iio] at hx hy
    have hxy' : (2 ^ x * M) % D / g = (2 ^ y * M) % D / g := hxy
    have hO : (2 ^ x * M) % D = (2 ^ y * M) % D := by
      have ex : (2 ^ x * M) % D = g * ((2 ^ x * M) % D / g) :=
        (Nat.mul_div_cancel' (hg_dvd_O x)).symm
      have ey : (2 ^ y * M) % D = g * ((2 ^ y * M) % D / g) :=
        (Nat.mul_div_cancel' (hg_dvd_O y)).symm
      rw [ex, ey, hxy']
    exact orbit_inj x y hx hy hO
  set s := (range p).image (fun j => (2 ^ j * M) % D / g) with hsdef
  have hcard : s.card = p := by rw [hsdef, Finset.card_image_of_injOn hrinj_on, card_range]
  have hpos : ∀ x ∈ s, 1 <= x := by
    intro x hx
    rw [hsdef] at hx
    rcases Finset.mem_image.1 hx with ⟨j, _, rfl⟩
    exact (Nat.one_le_div_iff hg_pos).2 (Nat.le_of_dvd (hOpos j) (hg_dvd_O j))
  -- the residues sum to q · wt(w)
  have hsumr : ∑ j ∈ range p, ((2 ^ j * M) % D / g) = q * periodWeight d p := by
    have h1 : ∑ j ∈ range p, (2 ^ j * M) % D
        = g * ∑ j ∈ range p, ((2 ^ j * M) % D / g) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => (Nat.mul_div_cancel' (hg_dvd_O j)).symm
    have h2 : ∑ j ∈ range p, (2 ^ j * M) % D = D * periodWeight d p :=
      sum_orbit_eq hp0 hd hMltD
    have h3 : g * ∑ j ∈ range p, ((2 ^ j * M) % D / g)
        = g * (q * periodWeight d p) := by
      rw [← h1, h2, hDgq]; ring
    exact Nat.eq_of_mul_eq_mul_left hg_pos h3
  -- triangular lower bound on the residue sum
  have htri := positive_finset_sum_ge_triangular s hcard hpos
  have hsi : ∑ x ∈ s, x = ∑ j ∈ range p, (2 ^ j * M) % D / g := by
    rw [hsdef]; exact Finset.sum_image hrinj_on
  rw [hsi, hsumr] at htri
  have hsum_final : p * (p + 1) <= 2 * q * periodWeight d p := by
    rw [Nat.mul_assoc]; exact htri
  have harith := orbit_digit_density_arithmetic hp0 hq_le hsum_final
  have hreal := orbit_digit_density_real_lower_third hQ hp0 harith
  unfold periodDensity
  exact hreal

end

end Erdos260
