/-
  P2 / trust-boundary audit: the SELF-CONTAINED pieces.

  This file discharges, as genuine Mathlib theorems, those trust-boundary
  hypotheses of `P1HotspotAudit` that are self-contained mathematics (i.e. do not
  depend on the carry-recurrence construction).  Each one removes an explicit
  hypothesis used in `P1HotspotAudit`.

  What is NOT here (and why): the remaining P2 items — package charged-summability
  (L.2), TRT/variation-drop compression (N), the stopped recurrence (I.2), and the
  *structural* trust boundaries (π_st injective on the real event carrier;
  R^{H5}_1 = 1_{Δ_B≠0}; priority heredity; phases tower-high & disjoint) — are NOT
  self-contained: they are statements about the actual digit sequence / coarea
  weights / priority map, so formalizing them means formalizing the construction
  itself.  Those are flagged in `P1HotspotAudit` as TRUST BOUNDARY and remain so.
-/
import Mathlib
import Erdos260.P1HotspotAudit

namespace Erdos260.P2TrustBoundary

open Finset

/-! ===========================================================================
    O3 trust boundary `htri`:  t distinct positive integers sum to ≥ t(t+1)/2.
    This discharges the `htri` hypothesis of `P1HotspotAudit.o3_density_floor_arith`
    (Lemma 24.1: the residues r_j ∈ {1,…,q-1} are distinct positives).
    =========================================================================== -/

theorem o3_triangular :
    ∀ (n : ℕ) (S : Finset ℕ), S.card = n → (∀ x ∈ S, 1 ≤ x) →
      n * (n + 1) ≤ 2 * ∑ x ∈ S, x := by
  intro n
  induction n with
  | zero =>
    intro S hcard _
    simp [Finset.card_eq_zero.mp hcard]
  | succ n ih =>
    intro S hcard hpos
    have hne : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
    set m := S.max' hne with hm
    have hmmem : m ∈ S := S.max'_mem hne
    have hsub : S ⊆ Finset.Icc 1 m :=
      fun x hx => Finset.mem_Icc.mpr ⟨hpos x hx, S.le_max' x hx⟩
    have hcardle : S.card ≤ m := by
      have h := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h; omega
    have hmge : n + 1 ≤ m := by rw [hcard] at hcardle; exact hcardle
    have hS'card : (S.erase m).card = n := by
      rw [Finset.card_erase_of_mem hmmem]; omega
    have hS'pos : ∀ x ∈ S.erase m, 1 ≤ x :=
      fun x hx => hpos x (Finset.mem_of_mem_erase hx)
    have ihS' := ih (S.erase m) hS'card hS'pos
    have hsum : ∑ x ∈ S, x = m + ∑ x ∈ S.erase m, x :=
      (Finset.add_sum_erase S (fun x => x) hmmem).symm
    rw [hsum]
    nlinarith [ihS', hmge]

/-- Packaged form matching `o3_density_floor_arith`'s `htri`: with the residue sum
    `= q*k`, the triangular bound becomes `t*(t+1) ≤ 2*(q*k)`. -/
theorem o3_htri_from_residues
    (q k : ℕ) (S : Finset ℕ) (hpos : ∀ x ∈ S, 1 ≤ x) (hsum : ∑ x ∈ S, x = q * k) :
    S.card * (S.card + 1) ≤ 2 * (q * k) := by
  have := o3_triangular S.card S rfl hpos
  rw [hsum] at this; exact this

/-! ===========================================================================
    E.6 / O1 trust boundary: outgoing-gap uniqueness.
    The recurrence interval `μ ∈ (2^{-g}, 2^{1-g})` (equivalently `1 < 2^g·μ < 2`)
    determines `g` uniquely, so a refined recurrent tower vertex has at most one
    recurrent outgoing visible gap (E.6 out-degree ≤ 1, the input to "recurrent
    SCC = simple directed cycle").
    =========================================================================== -/

theorem e6_slope_gap_unique (μ : ℝ) (hμ : 0 < μ) (g g' : ℕ)
    (hg : 1 < 2 ^ g * μ ∧ 2 ^ g * μ < 2)
    (hg' : 1 < 2 ^ g' * μ ∧ 2 ^ g' * μ < 2) :
    g = g' := by
  have key : ∀ a b : ℕ, a < b → 1 < 2 ^ a * μ → 2 ^ b * μ < 2 → False := by
    intro a b hab ha hb
    have hexp : b - a + a = b := Nat.sub_add_cancel (le_of_lt hab)
    have hbμ : (2 : ℝ) ^ b * μ = 2 ^ (b - a) * (2 ^ a * μ) := by
      rw [← mul_assoc, ← pow_add, hexp]
    have h2 : (2 : ℝ) ≤ 2 ^ (b - a) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (b - a) := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
    have hpos : (0 : ℝ) < 2 ^ a * μ := by positivity
    nlinarith [hbμ, h2, ha, hb, hpos]
  rcases lt_trichotomy g g' with h | h | h
  · exact (key g g' h hg.1 hg'.2).elim
  · exact h
  · exact (key g' g h hg'.1 hg.2).elim

/-! ===========================================================================
    O3 trust boundary (distinct residues): the doubling orbit
    `r_j = 2^j · a (mod q)` is injective for `j < ord_q(2)` (q odd, a a unit).
    This is the "the r_j are distinct" input to Lemma 24.1, hence to the §24
    fixed-pin density floor (g ≤ 3Q).
    =========================================================================== -/

theorem o3_doubling_orbit_injective {q : ℕ} [NeZero q] (u a : (ZMod q)ˣ) :
    Set.InjOn (fun j : ℕ => u ^ j * a) (Set.Iio (orderOf u)) := by
  intro j hj k hk hjk
  have h : u ^ j = u ^ k := by
    have := mul_right_cancel hjk
    simpa using this
  exact pow_injOn_Iio_orderOf hj hk h

/-! ===========================================================================
    CAPSTONE: O3 density floor with the triangular trust boundary DISCHARGED.
    Composes `o3_triangular` (this file) into `P1HotspotAudit.o3_density_floor_arith`,
    so the `htri` hypothesis is gone.  Remaining inputs are exactly the §24 facts:
    the residues are distinct positives (Finset + hpos), their sum is `q*k`
    (the carry long-division identity `2r_j = ε_{j+1} q + r_{j+1}` summed), and
    `q ≤ C·t` (the `q ≤ Q·p` bound).  Conclusion `t+1 ≤ 2Ck` is Lemma 24.1, the
    density floor `k/t ≥ 1/(2C) ≥ 1/(3Q)` behind `g ≤ 3Q`.
    =========================================================================== -/

theorem o3_density_floor_fully_discharged
    (q k C : ℕ) (S : Finset ℕ) (ht : 1 ≤ S.card)
    (hpos : ∀ x ∈ S, 1 ≤ x) (hsum : ∑ x ∈ S, x = q * k)
    (hqCt : q ≤ C * S.card) :
    S.card + 1 ≤ 2 * C * k :=
  Erdos260.P1HotspotAudit.o3_density_floor_arith q S.card k C ht
    (o3_htri_from_residues q k S hpos hsum) hqCt

end Erdos260.P2TrustBoundary
