import Erdos260.Elementary

/-!
# Basic objects for polynomial-scale windows

This module contains only the public semantics and scale-independent
combinatorial objects for the polynomial-window generalization.  The original
binary/affine development remains unchanged.
-/

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos260.PolynomialWindow

/-- Evaluation of a rational polynomial at a natural number, viewed in `ℝ`. -/
def polyEvalReal (p : Polynomial ℚ) (n : ℕ) : ℝ :=
  ((p.eval (n : ℚ) : ℚ) : ℝ)

/-- The `n`th summand of the polynomial-weighted base-`b` support series. -/
def polyWeightedTerm (b : ℕ) (p : Polynomial ℚ) (S : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ S then polyEvalReal p n / (b : ℝ) ^ n else 0

/-- The polynomial-weighted support series, with its ordinary `tsum` semantics. -/
def polyWeightedSeries (b : ℕ) (p : Polynomial ℚ) (S : Set ℕ) : ℝ :=
  ∑' n : ℕ, polyWeightedTerm b p S n

/-- Number of support points in the paper's half-open window `(N, N + W]`. -/
def windowCount (S : Set ℕ) (N W : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc N (N + W)).filter fun n => n ∈ S).card

/-- A positive gap between consecutive points of a support set. -/
def SetSupportGap (S : Set ℕ) (x g : ℕ) : Prop :=
  0 < g ∧ x ∈ S ∧ x + g ∈ S ∧
    ∀ n, x < n → n < x + g → n ∉ S

/-- The enumeration ratio is unbounded in the precise natural-number form
used by the irrationality corollary. -/
def EnumerationRatioUnbounded {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) : Prop :=
  ∀ C : ℕ, ∃ j : ℕ, C * (j + 1) < e.a j

/-- Ratio used in the definition of lower asymptotic density.

The value at `X = 0` is immaterial to the limit inferior. -/
def supportRatio (S : Set ℕ) (X : ℕ) : ℝ :=
  (Erdos260.supportCount S X : ℝ) / X

/-- Lower asymptotic density of a support set. -/
def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (supportRatio S) atTop

/-- Polynomial-scale window condition used by the public theorem. -/
def AdmissibleWindow (θ : ℝ) (N W : ℕ) : Prop :=
  0 < N ∧ Real.rpow (N : ℝ) θ ≤ (W : ℝ) ∧ W ≤ N

/-- Explicit quantifier form of uniform eventuality over admissible windows. -/
def UniformlyEventually (θ : ℝ) (P : ℕ → ℕ → Prop) : Prop :=
  ∃ N₀ : ℕ, ∀ N W : ℕ, N₀ ≤ N → AdmissibleWindow θ N W → P N W

/-- Explicit uniform little-`o` relation on polynomial-scale windows. -/
def UniformLittleO (θ : ℝ) (f g : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    UniformlyEventually θ fun N W => |f N W| ≤ ε * |g N W|

@[simp]
theorem polyWeightedTerm_not_mem (b : ℕ) (p : Polynomial ℚ)
    (S : Set ℕ) (n : ℕ) (hn : n ∉ S) :
    polyWeightedTerm b p S n = 0 := by
  simp [polyWeightedTerm, hn]

@[simp]
theorem polyWeightedTerm_mem (b : ℕ) (p : Polynomial ℚ)
    (S : Set ℕ) (n : ℕ) (hn : n ∈ S) :
    polyWeightedTerm b p S n = polyEvalReal p n / (b : ℝ) ^ n := by
  simp [polyWeightedTerm, hn]

@[simp]
theorem windowCount_zero (S : Set ℕ) (N : ℕ) :
    windowCount S N 0 = 0 := by
  simp [windowCount]

theorem windowCount_le_width (S : Set ℕ) (N W : ℕ) :
    windowCount S N W ≤ W := by
  classical
  unfold windowCount
  calc
    ((Finset.Ioc N (N + W)).filter fun n => n ∈ S).card ≤
        (Finset.Ioc N (N + W)).card := Finset.card_filter_le _ _
    _ = W := by simp

/-- The prefix support count never exceeds the length of the prefix. -/
theorem supportCount_le (S : Set ℕ) (X : ℕ) :
    Erdos260.supportCount S X ≤ X := by
  classical
  unfold Erdos260.supportCount
  calc
    ((Finset.Icc 1 X).filter fun n => n ∈ S).card ≤
        (Finset.Icc 1 X).card := Finset.card_filter_le _ _
    _ ≤ X := by simp

@[simp]
theorem supportCount_positiveSupport (S : Set ℕ) (X : ℕ) :
    Erdos260.supportCount (Erdos260.positiveSupport S) X =
      Erdos260.supportCount S X := by
  classical
  unfold Erdos260.supportCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Erdos260.positiveSupport,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hIcc, hS, _⟩
    exact ⟨hIcc, hS⟩
  · rintro ⟨hIcc, hS⟩
    exact ⟨hIcc, hS, hIcc.1⟩

/-- Exactly the first `j+1` points of an increasing positive enumeration lie
in the prefix ending at its `j`th value. -/
theorem supportCount_enumeration_apply {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) (j : ℕ) :
    Erdos260.supportCount S (e.a j) = j + 1 := by
  classical
  let emb : ℕ ↪ ℕ := ⟨e.a, e.strictMono.injective⟩
  have hfinset :
      (Finset.Icc 1 (e.a j)).filter (fun n => n ∈ S) =
        (Finset.range (j + 1)).map emb := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hnpos, hnle⟩, hnS⟩
      have hnRange : n ∈ Set.range e.a := by
        rw [e.range_eq]
        exact hnS
      obtain ⟨k, rfl⟩ := hnRange
      have hkj : k ≤ j := e.strictMono.le_iff_le.mp hnle
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have hkj : k ≤ j := by omega
      exact ⟨⟨e.positive k, e.strictMono.monotone hkj⟩, by
        rw [← e.range_eq]
        exact ⟨k, rfl⟩⟩
  unfold Erdos260.supportCount
  rw [hfinset, Finset.card_map, Finset.card_range]

/-- A window contained in `[1,X]` contributes to the prefix support count. -/
theorem windowCount_le_supportCount_of_add_le (S : Set ℕ)
    {N W X : ℕ} (hadd : N + W ≤ X) :
    windowCount S N W ≤ Erdos260.supportCount S X := by
  classical
  unfold windowCount Erdos260.supportCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨by omega, by omega⟩, hn.2⟩

theorem supportRatio_nonneg (S : Set ℕ) (X : ℕ) :
    0 ≤ supportRatio S X := by
  unfold supportRatio
  positivity

theorem supportRatio_le_one (S : Set ℕ) (X : ℕ) :
    supportRatio S X ≤ 1 := by
  by_cases hX : X = 0
  · simp [supportRatio, hX]
  · unfold supportRatio
    apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hX) :
      (0 : ℝ) < X)).2
    exact_mod_cast supportCount_le S X

theorem windowCount_mono_support {S T : Set ℕ} (hST : S ⊆ T) (N W : ℕ) :
    windowCount S N W ≤ windowCount T N W := by
  classical
  unfold windowCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

/-- Enlarging the right endpoint of a fixed half-open window cannot decrease
its support count. -/
theorem windowCount_mono_width (S : Set ℕ) (N : ℕ) {U W : ℕ}
    (hUW : U ≤ W) : windowCount S N U ≤ windowCount S N W := by
  classical
  unfold windowCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
  exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩

theorem admissibleWindow_width_pos {θ : ℝ} {N W : ℕ}
    (h : AdmissibleWindow θ N W) : 0 < W := by
  by_contra hW
  have hW0 : W = 0 := Nat.eq_zero_of_not_pos hW
  subst W
  have hNreal : (0 : ℝ) < N := by exact_mod_cast h.1
  have hrpow : 0 < Real.rpow (N : ℝ) θ := Real.rpow_pos_of_pos hNreal _
  simpa using lt_of_lt_of_le hrpow h.2.1

end Erdos260.PolynomialWindow
