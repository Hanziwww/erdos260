/-
  P1 Tier-1 leaves (batch B): further self-contained kernels for the Erdős-#260
  positive-density proof.

  This file is standalone (depends only on Mathlib plus the already-verified
  `Erdos260.P2TrustBoundary`).  Every theorem is genuine Lean with no `sorry`
  and no custom `axiom`; the `#print axioms` of each lands on the trusted base
  `[propext, Classical.choice, Quot.sound]`.

  Contents:
  * `tier3_cstar_choosable` — Convention 2.0f: after the positive calibration
    constants are fixed, a small `c_*` satisfying all four budget inequalities
    exists (Tier-3 constant consistency).
  * `lemma_24_1_core` / `lemma_24_1_ones_density` / `lemma_24_1_exists` —
    Lemma 24.1 (binary orbit digit density), END-TO-END: the doubling orbit
    residues are distinct positives (via `o3_doubling_orbit_injective`), the
    binary long-division step summed over a period gives `∑ r_j = q·k`, and the
    triangular bound (`o3_triangular`) yields `t(t+1) ≤ 2 q k`, i.e. the period
    of `a/q` has at least `(t+1)/(2q)` ones.
-/
import Mathlib
import Erdos260.P2TrustBoundary

namespace Erdos260.P1LeavesB

open Finset

/-! ===========================================================================
    LEAF 1 — Convention 2.0f Tier-3 constant choosability.
    After the positive constants `ε, c_pr, C_Q, C_*, ρ_D, κ, ξ` are fixed, the
    contradiction-density constant `c_*` can be chosen positive and small enough
    to satisfy all four budget inequalities of (2.0f) simultaneously.
    =========================================================================== -/

theorem tier3_cstar_choosable (Q : ℕ) (hQ : 1 ≤ Q) (ε cpr CQ Cstar ρD κ ξ : ℝ)
    (hε : 0 < ε) (hcpr : 0 < cpr) (hCQ : 0 < CQ) (hCstar : 0 < Cstar)
    (hρD : 0 < ρD) (hκ : 0 < κ) (hξ : 0 < ξ) :
    ∃ cstar : ℝ, 0 < cstar ∧ CQ * cstar < ξ * (ρD * κ) ∧
      Cstar * CQ * cstar < cpr / 4 ∧ 2 * cstar * ε ≤ (ξ / 6) * ρD ∧
      cstar < 1 / (6 * Q) := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have h6Q : (0 : ℝ) < 6 * (Q : ℝ) := by linarith
  -- the four positive upper bounds
  set a : ℝ := ξ * (ρD * κ) / CQ with ha_def
  set b : ℝ := cpr / (4 * (Cstar * CQ)) with hb_def
  set c : ℝ := (ξ / 6) * ρD / (2 * ε) with hc_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have hb_pos : 0 < b := by rw [hb_def]; positivity
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  have hd_pos : (0 : ℝ) < 1 / (6 * (Q : ℝ)) := div_pos one_pos h6Q
  -- take c_* = (min of the four)/2
  set m : ℝ := min a (min b (min c (1 / (6 * (Q : ℝ))))) with hm
  have hm_pos : 0 < m := by
    rw [hm]
    exact lt_min_iff.mpr ⟨ha_pos, lt_min_iff.mpr ⟨hb_pos, lt_min_iff.mpr ⟨hc_pos, hd_pos⟩⟩⟩
  have hma : m ≤ a := by rw [hm]; exact min_le_left _ _
  have hmb : m ≤ b := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmc : m ≤ c := by
    rw [hm]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmd : m ≤ 1 / (6 * (Q : ℝ)) := by
    rw [hm]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨m / 2, half_pos hm_pos, ?_, ?_, ?_, ?_⟩
  · -- CQ * c_* < ξ (ρD κ)
    have h : m / 2 < a := lt_of_lt_of_le (half_lt_self_iff.mpr hm_pos) hma
    rw [ha_def, lt_div_iff₀ hCQ] at h
    nlinarith [h]
  · -- C_* C_Q c_* < c_pr / 4
    have h : m / 2 < b := lt_of_lt_of_le (half_lt_self_iff.mpr hm_pos) hmb
    rw [hb_def, lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Cstar * CQ))] at h
    nlinarith [h]
  · -- 2 c_* ε ≤ (ξ/6) ρD
    have h : m / 2 < c := lt_of_lt_of_le (half_lt_self_iff.mpr hm_pos) hmc
    rw [hc_def, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)] at h
    nlinarith [h]
  · -- c_* < 1/(6Q)
    exact lt_of_lt_of_le (half_lt_self_iff.mpr hm_pos) hmd

/-! ===========================================================================
    LEAF 2 — Lemma 24.1 (binary orbit digit density), end to end.
    =========================================================================== -/

/-- Arithmetic core of Lemma 24.1.  Given a residue sequence `r` which on a
    period `[0, t)` is positive, injective, satisfies the binary long-division
    step `r (j+1) = (2 r_j) mod q`, and is `t`-periodic (`r t = r 0`), the digit
    count `k = ∑_{j<t} (2 r_j) / q` satisfies the density floor `t (t+1) ≤ 2 q k`.

    Proof: summing `2 r_j = q ε_{j+1} + r_{j+1}` over the period telescopes to
    `∑ r_j = q k`; the `t` distinct positive residues sum to `≥ t(t+1)/2`
    (`o3_triangular`). -/
theorem lemma_24_1_core
    (q t : ℕ) (r : ℕ → ℕ)
    (hpos : ∀ j, j < t → 1 ≤ r j)
    (hstep : ∀ j, j < t → r (j + 1) = (2 * r j) % q)
    (hper : r t = r 0)
    (hinj : Set.InjOn r (Set.Iio t)) :
    t * (t + 1) ≤ 2 * (q * ∑ j ∈ Finset.range t, (2 * r j) / q) := by
  classical
  have hinj_coe : Set.InjOn r ↑(Finset.range t) := by
    rw [Finset.coe_range]; exact hinj
  -- cyclic-shift identity ∑ r_{j+1} = ∑ r_j
  have hshift : ∑ j ∈ Finset.range t, r (j + 1) = ∑ j ∈ Finset.range t, r j := by
    have h1 := Finset.sum_range_succ r t
    have h2 := Finset.sum_range_succ' r t
    have h3 : (∑ j ∈ Finset.range t, r j) + r t
            = (∑ j ∈ Finset.range t, r (j + 1)) + r 0 := by rw [← h1, h2]
    rw [hper] at h3
    omega
  -- 2 S = q K + S
  have hsum_id : 2 * (∑ j ∈ Finset.range t, r j)
      = q * (∑ j ∈ Finset.range t, (2 * r j) / q) + (∑ j ∈ Finset.range t, r j) := by
    have e1 : ∑ j ∈ Finset.range t, (2 * r j)
            = ∑ j ∈ Finset.range t, (q * ((2 * r j) / q) + r (j + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      have hdm := Nat.div_add_mod (2 * r j) q
      rw [hstep j hjt]
      omega
    calc 2 * (∑ j ∈ Finset.range t, r j)
        = ∑ j ∈ Finset.range t, (2 * r j) := by rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range t, (q * ((2 * r j) / q) + r (j + 1)) := e1
      _ = (∑ j ∈ Finset.range t, q * ((2 * r j) / q))
            + ∑ j ∈ Finset.range t, r (j + 1) := by rw [Finset.sum_add_distrib]
      _ = q * (∑ j ∈ Finset.range t, (2 * r j) / q) + ∑ j ∈ Finset.range t, r (j + 1) := by
            rw [Finset.mul_sum]
      _ = q * (∑ j ∈ Finset.range t, (2 * r j) / q) + ∑ j ∈ Finset.range t, r j := by rw [hshift]
  have hSeq : (∑ j ∈ Finset.range t, r j)
      = q * (∑ j ∈ Finset.range t, (2 * r j) / q) := by omega
  -- the t distinct positive residues
  have hcard : (Finset.image r (Finset.range t)).card = t := by
    rw [Finset.card_image_of_injOn hinj_coe, Finset.card_range]
  have hpos_img : ∀ x ∈ Finset.image r (Finset.range t), 1 ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hpos j (Finset.mem_range.mp hj)
  have htri := Erdos260.P2TrustBoundary.o3_triangular t
    (Finset.image r (Finset.range t)) hcard hpos_img
  have hsum_img : ∑ x ∈ Finset.image r (Finset.range t), x = ∑ j ∈ Finset.range t, r j :=
    Finset.sum_image hinj_coe
  rw [hsum_img, hSeq] at htri
  exact htri

/-- Lemma 24.1.  Let `q ≥ 3`, let `u, a` be units of `ZMod q` with `(u : ZMod q) = 2`
    (so `u` is the doubling), and let `t = orderOf u = ord_q(2)`.  Writing
    `r_j = ((u^j a : ZMod q)).val ∈ {1, …, q-1}` for the residues and
    `k = ∑_{j<t} (2 r_j)/q` for the number of binary 1-digits in the period of
    `a/q`, we have `t (t+1) ≤ 2 q k`, i.e. the period has density of ones
    `k/t ≥ (t+1)/(2 q)`. -/
theorem lemma_24_1_ones_density {q : ℕ} (hq : 3 ≤ q) (u a : (ZMod q)ˣ)
    (hu : (u : ZMod q) = 2) :
    orderOf u * (orderOf u + 1) ≤
      2 * (q * ∑ j ∈ Finset.range (orderOf u),
              (2 * ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val) / q) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hval2 : ((2 : ZMod q)).val = 2 := by
    have h : ((2 : ℕ) : ZMod q) = (2 : ZMod q) := by norm_cast
    rw [← h, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have hpos : ∀ j, j < orderOf u → 1 ≤ ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val := by
    intro j _
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hx0 : ((u ^ j * a : (ZMod q)ˣ) : ZMod q) = 0 :=
      ZMod.val_injective q (by rw [ZMod.val_zero]; exact hzero)
    exact (Units.ne_zero (u ^ j * a)) hx0
  have hstep : ∀ j, j < orderOf u →
      ((u ^ (j + 1) * a : (ZMod q)ˣ) : ZMod q).val
        = (2 * ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val) % q := by
    intro j _
    have hunit : (u ^ (j + 1) * a : (ZMod q)ˣ) = u * (u ^ j * a) := by
      rw [pow_succ', mul_assoc]
    have hx : ((u ^ (j + 1) * a : (ZMod q)ˣ) : ZMod q)
            = (2 : ZMod q) * ((u ^ j * a : (ZMod q)ˣ) : ZMod q) := by
      rw [hunit]; push_cast; rw [hu]
    rw [hx, ZMod.val_mul, hval2]
  have hper : ((u ^ (orderOf u) * a : (ZMod q)ˣ) : ZMod q).val
            = ((u ^ 0 * a : (ZMod q)ˣ) : ZMod q).val := by
    have hunit : (u ^ (orderOf u) * a : (ZMod q)ˣ) = (u ^ 0 * a : (ZMod q)ˣ) := by
      rw [pow_orderOf_eq_one, pow_zero]
    rw [hunit]
  have hinj : Set.InjOn (fun j : ℕ => ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val)
      (Set.Iio (orderOf u)) := by
    intro x hx y hy hxy
    have h1 : ((u ^ x * a : (ZMod q)ˣ) : ZMod q) = ((u ^ y * a : (ZMod q)ˣ) : ZMod q) :=
      ZMod.val_injective q hxy
    have h2 : (u ^ x * a : (ZMod q)ˣ) = (u ^ y * a : (ZMod q)ˣ) := Units.ext h1
    exact Erdos260.P2TrustBoundary.o3_doubling_orbit_injective u a hx hy h2
  exact lemma_24_1_core q (orderOf u)
    (fun j => ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val) hpos hstep hper hinj

/-- Lemma 24.1 packaged for odd `q ≥ 3`: the doubling unit `2 ∈ (ZMod q)ˣ`
    exists, and for any unit `a` the period of `a/q` has at least `(t+1)/(2q)`
    binary 1-digits. -/
theorem lemma_24_1_exists {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (a : (ZMod q)ˣ) :
    ∃ u : (ZMod q)ˣ, (u : ZMod q) = 2 ∧
      orderOf u * (orderOf u + 1) ≤
        2 * (q * ∑ j ∈ Finset.range (orderOf u),
                (2 * ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val) / q) := by
  have hcop : Nat.Coprime 2 q := hodd.coprime_two_left
  have hu : ((ZMod.unitOfCoprime 2 hcop : (ZMod q)ˣ) : ZMod q) = 2 := by
    rw [ZMod.coe_unitOfCoprime]; norm_cast
  exact ⟨ZMod.unitOfCoprime 2 hcop, hu, lemma_24_1_ones_density hq _ a hu⟩

/-! ===========================================================================
    LEAF 3 — O4 character-orthogonality floor.
    For a finite abelian group `G`, the off-neutral indicator `1_{δ ≠ 0}` equals
    the Fourier expression `1 - |G|⁻¹ ∑_χ χ(δ)`.  This is dual additive-character
    orthogonality (`AddChar.sum_apply_eq_ite`, the Pontryagin-duality form
    `∑_χ χ(δ) = |G|·1_{δ=0}`), i.e. the spectral form of the O4.b class-1
    valuation floor `ϑ₁ = 1_{Δ_B ≠ 0}`.
    =========================================================================== -/

theorem o4_character_floor {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (δ : G) :
    1 - (1 / (Fintype.card G : ℂ)) * ∑ χ : AddChar G ℂ, χ δ
      = if δ = 0 then (0 : ℂ) else 1 := by
  haveI : Nonempty G := ⟨0⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [AddChar.sum_apply_eq_ite]
  split_ifs with h
  · rw [one_div, inv_mul_cancel₀ hcard, sub_self]
  · rw [mul_zero, sub_zero]

/-- Equivalent packaging of `o4_character_floor` matching `P1HotspotAudit.w1`:
    the Fourier expression evaluates to `0` on the neutral class and `1` off it. -/
theorem o4_character_floor_eq_indicator
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (δ : G) :
    (1 / (Fintype.card G : ℂ)) * ∑ χ : AddChar G ℂ, χ δ = if δ = 0 then (1 : ℂ) else 0 := by
  haveI : Nonempty G := ⟨0⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [AddChar.sum_apply_eq_ite]
  split_ifs with h
  · rw [one_div, inv_mul_cancel₀ hcard]
  · rw [mul_zero]

/-! ===========================================================================
    LEAF 4 — Fine–Wilf periodicity (K.2 overlap ⇒ common gcd-period).
    Mathlib supplies the periodicity (Fine–Wilf) theorem as `List.HasPeriod.gcd`.
    We record the K.2-relevant corollaries: two overlapping period descriptions
    of total overlap `≥ p + q − gcd(p,q)` force the common period `gcd(p,q)`, and
    the coprime case forces a constant (period-1) word.
    =========================================================================== -/

/-- **Fine–Wilf theorem** (K.2 corollary).  A word `w` with two periods `p, q`
    whose overlap reaches the Fine–Wilf threshold `p + q − gcd(p,q)` also has the
    common period `gcd(p,q)`. -/
theorem fine_wilf {α : Type*} {w : List α} {p q : ℕ}
    (hp : w.HasPeriod p) (hq : w.HasPeriod q)
    (hlen : p + q - Nat.gcd p q ≤ w.length) :
    w.HasPeriod (Nat.gcd p q) :=
  hp.gcd hq hlen

/-- K.2 special case: two *coprime* overlapping periods of total overlap
    `≥ p + q − 1` force a constant (period-1) word. -/
theorem fine_wilf_coprime {α : Type*} {w : List α} {p q : ℕ}
    (hp : w.HasPeriod p) (hq : w.HasPeriod q) (hcop : Nat.Coprime p q)
    (hlen : p + q - 1 ≤ w.length) :
    w.HasPeriod 1 := by
  have hg : Nat.gcd p q = 1 := hcop
  have h := hp.gcd hq (by rw [hg]; exact hlen)
  rwa [hg] at h

end Erdos260.P1LeavesB
