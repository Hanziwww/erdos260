import Mathlib
import Erdos260.HitSequence
import Erdos260.Pressure

/-!
# Window-sum lower bound (manuscript Lemma 21.1, §21)

This file proves the manuscript inequality

`∑_{k ∈ Ico i (i + K)} (a(k + r + 1) − a k) ≥ (r + 1) · X − (r + 1)² · maxGap`

for a strictly monotone `a : ℕ → ℕ`, given:

- `K ≥ r + 1` (enough hits in the shell window);
- `a(i + K) > 2X` (the next hit after the shell exceeds `2X`);
- `a(i − 1) ≤ X` and `i ≥ 1` (there is a hit before the shell);
- hit gaps in `[i − 1, i + r)` are bounded by `maxGap`.

The proof has two steps:

1. **Telescoping identity** (`sum_Ico_a_window_telescope`): rewrites the
   window sum as `∑_{l < r+1} a(i+K+l) − ∑_{l < r+1} a(i+l)` (in `ℤ`,
   to handle `Nat` subtraction safely).

2. **Boundary bounds**: lower-bound each summand of the first sum by
   `a(i+K)` and upper-bound each summand of the second sum by `a(i+r)`,
   then use the cumulative gap bound from `HitSequence.a_add_le_of_hitGap_le`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### Telescoping identity for hit-window sums -/

/--
**Telescoping identity for hit-window sums.**

For strictly monotone `a : ℕ → ℕ`, with `K ≥ r + 1`,

`∑_{k ∈ Ico i (i + K)} (a(k + r + 1) − a k : ℤ) =
  ∑_{l ∈ range (r + 1)} a(i + K + l) − ∑_{l ∈ range (r + 1)} a(i + l)`.

This is the manuscript step that converts a window-sum into a boundary
correction: the bulk middle terms cancel.
-/
theorem sum_Ico_a_window_telescope
    {a : Nat → Nat} (hmono : StrictMono a) (i K r : Nat) (hKr : r + 1 ≤ K) :
    ∑ k ∈ Finset.Ico i (i + K), ((a (k + r + 1) - a k : Nat) : ℤ) =
      (∑ l ∈ Finset.range (r + 1), (a (i + K + l) : ℤ))
        - ∑ l ∈ Finset.range (r + 1), (a (i + l) : ℤ) := by
  -- Cast each Nat subtraction to Int subtraction (with monotonicity witness).
  have h_le_term : ∀ k, a k ≤ a (k + r + 1) :=
    fun k => hmono.monotone (by omega)
  have h_term :
      (∑ k ∈ Finset.Ico i (i + K), ((a (k + r + 1) - a k : Nat) : ℤ)) =
        (∑ k ∈ Finset.Ico i (i + K), (a (k + r + 1) : ℤ)) -
          (∑ k ∈ Finset.Ico i (i + K), (a k : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Int.natCast_sub (h_le_term k)]
  rw [h_term]
  -- Re-index the first sum: `k + r + 1` ranges over `Ico (i+r+1) (i+K+r+1)`.
  have h_reindex :
      (∑ k ∈ Finset.Ico i (i + K), (a (k + r + 1) : ℤ)) =
        ∑ m ∈ Finset.Ico (i + r + 1) (i + K + r + 1), (a m : ℤ) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have h_eq1 : i + K - i = K := by omega
    have h_eq2 : i + K + r + 1 - (i + r + 1) = K := by omega
    rw [h_eq1, h_eq2]
    apply Finset.sum_congr rfl
    intro l _
    have h_idx : i + l + r + 1 = i + r + 1 + l := by ring
    rw [h_idx]
  rw [h_reindex]
  -- Split each sum at the overlap boundary.
  have h_split_first :
      (∑ m ∈ Finset.Ico (i + r + 1) (i + K + r + 1), (a m : ℤ)) =
        (∑ m ∈ Finset.Ico (i + r + 1) (i + K), (a m : ℤ)) +
          ∑ m ∈ Finset.Ico (i + K) (i + K + r + 1), (a m : ℤ) :=
    (Finset.sum_Ico_consecutive (fun m => (a m : ℤ))
        (show i + r + 1 ≤ i + K by omega)
        (show i + K ≤ i + K + r + 1 by omega)).symm
  have h_split_second :
      (∑ k ∈ Finset.Ico i (i + K), (a k : ℤ)) =
        (∑ k ∈ Finset.Ico i (i + r + 1), (a k : ℤ)) +
          ∑ k ∈ Finset.Ico (i + r + 1) (i + K), (a k : ℤ) :=
    (Finset.sum_Ico_consecutive (fun m => (a m : ℤ))
        (show i ≤ i + r + 1 by omega)
        (show i + r + 1 ≤ i + K by omega)).symm
  rw [h_split_first, h_split_second]
  -- Convert boundary `Ico` sums to `range` sums.
  have h_high :
      (∑ m ∈ Finset.Ico (i + K) (i + K + r + 1), (a m : ℤ)) =
        ∑ l ∈ Finset.range (r + 1), (a (i + K + l) : ℤ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h_eq : i + K + r + 1 - (i + K) = r + 1 := by omega
    rw [h_eq]
  have h_low :
      (∑ k ∈ Finset.Ico i (i + r + 1), (a k : ℤ)) =
        ∑ l ∈ Finset.range (r + 1), (a (i + l) : ℤ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h_eq : i + r + 1 - i = r + 1 := by omega
    rw [h_eq]
  rw [h_high, h_low]
  -- The middle `Ico (i+r+1) (i+K)` sums cancel after distribution.
  ring

/-! ### Main window-sum lower bound -/

/--
**Manuscript Lemma 21.1 (window-sum lower bound).**

For a `HitSequence d a`, with parameters `i, X, r, maxGap, K` satisfying:

- `K ≥ r + 1` (enough hits in the window),
- `1 ≤ i` (the shell starts after the first hit),
- `a (i - 1) ≤ X` (the hit before the shell is at most `X`),
- `2X + 1 ≤ a (i + K)` (the hit after the shell exceeds `2X`),
- every hit gap in `[i − 1, i + r)` is at most `maxGap`,

we have the lower bound

  `(r + 1) · X − (r + 1)² · maxGap ≤
     ∑_{k ∈ Ico i (i + K)} (a(k + r + 1) − a k)`.
-/
theorem windowSumLower_proof
    {d a : Nat → Nat} (hseq : HitSequence d a)
    {i X r maxGap K : Nat}
    (hKr : r + 1 ≤ K)
    (h_first_pos : 1 ≤ i)
    (h_a_im1_le : a (i - 1) ≤ X)
    (h_a_iK_gt : 2 * X + 1 ≤ a (i + K))
    (h_gap_le : ∀ k, i - 1 ≤ k → k < i + r → hitGap a k ≤ maxGap) :
    ((r : ℝ) + 1) * (X : ℝ)
        - ((r : ℝ) + 1) ^ 2 * (maxGap : ℝ) ≤
      ∑ k ∈ Finset.Ico i (i + K),
        ((a (k + r + 1) - a k : Nat) : ℝ) := by
  -- Telescoping identity (in `ℤ`).
  have h_tel := sum_Ico_a_window_telescope hseq.strict i K r hKr
  -- High boundary lower bound: `∑ a(i+K+l) ≥ (r+1) · a(i+K) ≥ (r+1)·(2X+1)`.
  have h_high_low :
      ((r : ℤ) + 1) * (a (i + K) : ℤ) ≤
        ∑ l ∈ Finset.range (r + 1), (a (i + K + l) : ℤ) := by
    have h_const :
        (∑ _l ∈ Finset.range (r + 1), (a (i + K) : ℤ)) =
          ((r : ℤ) + 1) * (a (i + K) : ℤ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    calc ((r : ℤ) + 1) * (a (i + K) : ℤ)
        = ∑ _l ∈ Finset.range (r + 1), (a (i + K) : ℤ) := h_const.symm
      _ ≤ ∑ l ∈ Finset.range (r + 1), (a (i + K + l) : ℤ) := by
          apply Finset.sum_le_sum
          intro l _
          exact_mod_cast
            hseq.strict.monotone (by omega : i + K ≤ i + K + l)
  -- Cumulative gap bound: `a(i+r) ≤ a(i-1) + (r+1)·maxGap ≤ X + (r+1)·maxGap`.
  have h_a_ir_le : a (i + r) ≤ X + (r + 1) * maxGap := by
    have h_im1_plus : (i - 1) + (r + 1) = i + r := by omega
    have h_aux :
        a ((i - 1) + (r + 1)) ≤ a (i - 1) + (r + 1) * maxGap :=
      hseq.a_add_le_of_hitGap_le (fun k hk1 hk2 =>
        h_gap_le k hk1 (by omega))
    rw [h_im1_plus] at h_aux
    omega
  -- Low boundary upper bound: `∑ a(i+l) ≤ (r+1) · a(i+r)`.
  have h_low_upp :
      ∑ l ∈ Finset.range (r + 1), (a (i + l) : ℤ) ≤
        ((r : ℤ) + 1) * (a (i + r) : ℤ) := by
    have h_const :
        (∑ _l ∈ Finset.range (r + 1), (a (i + r) : ℤ)) =
          ((r : ℤ) + 1) * (a (i + r) : ℤ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    calc ∑ l ∈ Finset.range (r + 1), (a (i + l) : ℤ)
        ≤ ∑ _l ∈ Finset.range (r + 1), (a (i + r) : ℤ) := by
          apply Finset.sum_le_sum
          intro l hl
          rw [Finset.mem_range] at hl
          exact_mod_cast
            hseq.strict.monotone (by omega : i + l ≤ i + r)
      _ = ((r : ℤ) + 1) * (a (i + r) : ℤ) := h_const
  -- High and low extremes cast to ℤ.
  have h_high_2X1 :
      ((r : ℤ) + 1) * (2 * X + 1) ≤ ((r : ℤ) + 1) * (a (i + K) : ℤ) := by
    have h_nn : (0 : ℤ) ≤ (r : ℤ) + 1 := by positivity
    have h_le : (2 * X + 1 : ℤ) ≤ (a (i + K) : ℤ) := by exact_mod_cast h_a_iK_gt
    exact mul_le_mul_of_nonneg_left h_le h_nn
  have h_low_X :
      ((r : ℤ) + 1) * (a (i + r) : ℤ) ≤
        ((r : ℤ) + 1) * ((X : ℤ) + ((r : ℤ) + 1) * (maxGap : ℤ)) := by
    have h_nn : (0 : ℤ) ≤ (r : ℤ) + 1 := by positivity
    have h_le : (a (i + r) : ℤ) ≤ (X : ℤ) + ((r : ℤ) + 1) * (maxGap : ℤ) := by
      exact_mod_cast h_a_ir_le
    exact mul_le_mul_of_nonneg_left h_le h_nn
  -- Combine in `ℤ`.
  have h_z :
      ((r : ℤ) + 1) * (X : ℤ) - ((r : ℤ) + 1) ^ 2 * (maxGap : ℤ) ≤
        ∑ k ∈ Finset.Ico i (i + K),
          ((a (k + r + 1) - a k : Nat) : ℤ) := by
    rw [h_tel]
    linarith [h_high_low, h_high_2X1, h_low_upp, h_low_X]
  -- Cast `ℤ → ℝ`.
  exact_mod_cast h_z

/-! ### Coarse low-excess upper bound -/

/--
**Coarse low-excess upper bound.**

For any starts of the form `Finset.Ico i (i + K)` and any threshold pair
`(T, Y)` with `0 ≤ Y`, the manuscript low-excess mass on the complement
of the high-excess starts is bounded by `K · Y`:

  `highExcessMass (Ico i (i + K) \ highExcessStarts …) (hitGap a) r T ≤
     K · Y`.

This follows from `highExcessMass_sdiff_highExcessStarts_le_card_mul`
(`≤ (sdiff.card : ℝ) · Y`) by loosening `sdiff.card ≤ Ico.card = K`.

The bound is **not the manuscript-tight** `O(c₀ ε² X L²)` from
`proof_v2.tex` §21, but it is **real** and downstream consumers that
choose `lowExcessBound = K · Y` get a proved `lowExcessUpper` field
"for free".
-/
theorem lowExcessUpper_KY_bound
    {a : Nat → Nat} (i K r : Nat) (T Y : ℝ) (hY : 0 ≤ Y) :
    highExcessMass
      (Finset.Ico i (i + K) \
        highExcessStarts (Finset.Ico i (i + K)) (hitGap a) r T Y)
      (hitGap a) r T ≤ (K : ℝ) * Y := by
  have h_base :=
    highExcessMass_sdiff_highExcessStarts_le_card_mul
      (starts := Finset.Ico i (i + K)) (g := hitGap a)
      (r := r) (T := T) (Y := Y)
  have h_card_le :
      (((Finset.Ico i (i + K) \
          highExcessStarts (Finset.Ico i (i + K)) (hitGap a) r T Y).card
            : Nat) : ℝ) ≤ (((Finset.Ico i (i + K)).card : Nat) : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have h_card_eq : (Finset.Ico i (i + K)).card = K := by
    rw [Nat.card_Ico]; omega
  have h_mul_le :
      (((Finset.Ico i (i + K) \
          highExcessStarts (Finset.Ico i (i + K)) (hitGap a) r T Y).card
            : Nat) : ℝ) * Y ≤
        (((Finset.Ico i (i + K)).card : Nat) : ℝ) * Y :=
    mul_le_mul_of_nonneg_right h_card_le hY
  have h_rewrite :
      (((Finset.Ico i (i + K)).card : Nat) : ℝ) * Y = (K : ℝ) * Y := by
    rw [h_card_eq]
  linarith

/--
**Manuscript-scaled low-excess upper bound under failure.**

Under the failure hypothesis `K ≤ c₀ · X` (manuscript `A(2X) − A(X) ≤ c₀ X`,
`proof_v2.tex` line 291), the per-`T` low-excess mass is bounded by
`c₀ · X · Y`.

Taking the manuscript window threshold `Y = εL` gives the per-`T` form
`c₀ ε X L` of the low-excess layer of `proof_v2.tex` line 306.  The
manuscript's fully-integrated `O(c₀ ε² X L²)` arises by integrating this
per-`T` bound over the threshold window `I = [T₀, T₀ + c_I L]` of length
`|I| ≍ L`; that extra factor of `L` lives in the integrated-vs-per-`T`
encoding handled by the global assembly (κ-fidelity, roadmap P10).

This makes the dependence on the *failure* constant `c₀` explicit, replacing
the coarse `K · Y` of `lowExcessUpper_KY_bound`.
-/
theorem lowExcessUpper_failure_bound
    {a : Nat → Nat} (i K r : Nat) (T Y c0 X : ℝ)
    (hY : 0 ≤ Y) (hfail : (K : ℝ) ≤ c0 * X) :
    highExcessMass
      (Finset.Ico i (i + K) \
        highExcessStarts (Finset.Ico i (i + K)) (hitGap a) r T Y)
      (hitGap a) r T ≤ c0 * X * Y := by
  have h1 := lowExcessUpper_KY_bound (a := a) i K r T Y hY
  have h2 : (K : ℝ) * Y ≤ c0 * X * Y := by
    have := mul_le_mul_of_nonneg_right hfail hY
    linarith [this]
  linarith

end

end Erdos260
