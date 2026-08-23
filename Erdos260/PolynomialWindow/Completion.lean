import Erdos260.PolynomialWindow.Exterior
import Erdos260.PolynomialWindow.Interior
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Completion of the polynomial-window argument

This module begins with the public normalization bridge.  It converts the
`Polynomial ℚ` statement into the integral carry system used by the internal
modules without changing the support set or hiding a finite exceptional tail.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos260.PolynomialWindow

/-! ## Rational-to-integral carry bridge -/

/-- Evaluation of an integral normalization over `ℝ`. -/
theorem IntegralNormalization.eval_real_eq {p : Polynomial ℚ}
    (h : IntegralNormalization p) (n : ℕ) :
    (intPolynomialValue h.poly n : ℝ) =
      (h.multiplier : ℝ) * polyEvalReal p n := by
  have hq := h.eval_map_eq (n : ℚ)
  have hmap :
      ((h.poly.eval (n : ℤ) : ℤ) : ℚ) =
        (h.poly.map (algebraMap ℤ ℚ)).eval (n : ℚ) := by
    exact (Polynomial.eval_map_apply (p := h.poly)
      (f := algebraMap ℤ ℚ) (n : ℤ)).symm
  have hrat :
      ((h.poly.eval (n : ℤ) : ℤ) : ℚ) =
        (h.multiplier : ℚ) * p.eval (n : ℚ) := by
    rw [hmap, hq]
  unfold intPolynomialValue polyEvalReal
  exact_mod_cast hrat

/-- Clearing denominators and changing the overall sign preserve the degree
of the public rational polynomial. -/
theorem IntegralNormalization.natDegree_eq {p : Polynomial ℚ}
    (h : IntegralNormalization p) :
    h.poly.natDegree = p.natDegree := by
  have hmap :
      (h.poly.map (algebraMap ℤ ℚ)).natDegree = h.poly.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective ℤ ℚ) h.poly
  have hmult : (h.multiplier : ℚ) ≠ 0 := by
    exact_mod_cast h.multiplier_ne_zero
  calc
    h.poly.natDegree =
        (h.poly.map (algebraMap ℤ ℚ)).natDegree := hmap.symm
    _ = ((h.multiplier : ℚ) • p).natDegree :=
      congrArg Polynomial.natDegree h.map_eq
    _ = p.natDegree := p.natDegree_smul hmult

/-- The real polynomial attached to a normalization evaluates to the same
integer value. -/
theorem IntegralNormalization.realPoly_eval_nat {p : Polynomial ℚ}
    (h : IntegralNormalization p) (n : ℕ) :
    h.realPoly.eval (n : ℝ) = (intPolynomialValue h.poly n : ℝ) := by
  unfold IntegralNormalization.realPoly intPolynomialValue
  exact Polynomial.eval_map_apply (p := h.poly)
    (f := algebraMap ℤ ℝ) (n : ℤ)

/-- Pointwise compatibility of the public summand with denominator clearing. -/
theorem IntegralNormalization.integralWeightedTerm_eq {p : Polynomial ℚ}
    (h : IntegralNormalization p) (b : ℕ) (S : Set ℕ) (n : ℕ) :
    integralWeightedTerm b h.poly S n =
      (h.multiplier : ℝ) * polyWeightedTerm b p S n := by
  classical
  by_cases hn : n ∈ S
  · rw [integralWeightedTerm, polyWeightedTerm, if_pos hn, if_pos hn,
      h.eval_real_eq]
    ring
  · simp [integralWeightedTerm, polyWeightedTerm, hn]

/-- A chosen integral normalization and its eventual positivity cutoff produce
the exact carry system used by the internal proof. -/
def IntegralNormalization.toCarrySeries {p : Polynomial ℚ}
    (h : IntegralNormalization p) (b : ℕ) (hb : 2 ≤ b)
    (S : Set ℕ) (hS : S.Infinite) (η : ℚ)
    (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ)) : CarrySeries := by
  let N0 := Classical.choose h.eventually_eval_nat_pos
  have hN0 := Classical.choose_spec h.eventually_eval_nat_pos
  refine
    { base := b
      base_ge_two := hb
      weight := h.poly
      weight_ne_zero := h.poly_ne_zero
      support := S
      support_infinite := hS
      value := (h.multiplier : ℚ) * η
      hasSum := ?_
      positiveFrom := N0
      weight_pos := ?_ }
  · have hscaled := hsum.mul_left (h.multiplier : ℝ)
    have hfun :
        (fun n : ℕ => (h.multiplier : ℝ) * polyWeightedTerm b p S n) =
          integralWeightedTerm b h.poly S := by
      funext n
      exact (h.integralWeightedTerm_eq b S n).symm
    rw [hfun] at hscaled
    simpa using hscaled
  · intro n hn
    have hreal : 0 < h.realPoly.eval (n : ℝ) := hN0 n hn
    rw [h.realPoly_eval_nat] at hreal
    exact_mod_cast hreal

/-- Public inputs always admit an integral carry system with exactly the same
base and support. -/
theorem exists_normalizedCarrySeries {b : ℕ} (hb : 2 ≤ b)
    {p : Polynomial ℚ} (hp : p ≠ 0) (S : Set ℕ) (hS : S.Infinite)
    (η : ℚ) (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ)) :
    ∃ h : IntegralNormalization p, ∃ D : CarrySeries,
      D = h.toCarrySeries b hb S hS η hsum ∧
        D.base = b ∧ D.support = S := by
  let h := Classical.choice (exists_integralNormalization hp)
  let D := h.toCarrySeries b hb S hS η hsum
  exact ⟨h, D, rfl, rfl, rfl⟩

/-! ## Removing a finite prefix and shifting the tail -/

/-- Support after deleting the first `e` indices and translating the tail
back to the origin. -/
def shiftedSupport (S : Set ℕ) (e : ℕ) : Set ℕ :=
  {n | n + e ∈ S}

theorem shiftedSupport_infinite {S : Set ℕ} (hS : S.Infinite) (e : ℕ) :
    (shiftedSupport S e).Infinite := by
  intro hfinite
  have himage : ((fun n : ℕ => n + e) '' shiftedSupport S e).Finite :=
    hfinite.image _
  have hsmall : ((Finset.range e : Finset ℕ) : Set ℕ).Finite :=
    Finset.finite_toSet _
  apply hS
  apply (hsmall.union himage).subset
  intro n hn
  by_cases hne : n < e
  · left
    simpa using hne
  · right
    have hen : e ≤ n := Nat.le_of_not_gt hne
    refine ⟨n - e, ?_, Nat.sub_add_cancel hen⟩
    show n - e + e ∈ S
    rw [Nat.sub_add_cancel hen]
    exact hn

/-- Polynomial weight after translating an index by `e`. -/
def shiftedIntegralPolynomial (w : Polynomial ℤ) (e : ℕ) : Polynomial ℤ :=
  w.comp (Polynomial.X + Polynomial.C (e : ℤ))

theorem shiftedIntegralPolynomial_eval (w : Polynomial ℤ) (e n : ℕ) :
    intPolynomialValue (shiftedIntegralPolynomial w e) n =
      intPolynomialValue w (n + e) := by
  simp [shiftedIntegralPolynomial, intPolynomialValue,
    Polynomial.eval_comp]

theorem shiftedIntegralPolynomial_natDegree (w : Polynomial ℤ) (e : ℕ) :
    (shiftedIntegralPolynomial w e).natDegree = w.natDegree := by
  have hlinear :
      (Polynomial.X + Polynomial.C (e : ℤ) : Polynomial ℤ).natDegree = 1 :=
    Polynomial.natDegree_X_add_C _
  rw [shiftedIntegralPolynomial, Polynomial.natDegree_comp, hlinear, mul_one]

/-- Translating the argument of an integral polynomial preserves its leading
coefficient. -/
theorem shiftedIntegralPolynomial_leadingCoeff (w : Polynomial ℤ) (e : ℕ) :
    (shiftedIntegralPolynomial w e).leadingCoeff = w.leadingCoeff := by
  have hlinear :
      (Polynomial.X + Polynomial.C (e : ℤ) : Polynomial ℤ).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_add_C]
    exact one_ne_zero
  rw [shiftedIntegralPolynomial, Polynomial.leadingCoeff_comp hlinear,
    Polynomial.monic_X_add_C, one_pow, mul_one]

theorem shiftedIntegralPolynomial_ne_zero {w : Polynomial ℤ} (hw : w ≠ 0)
    (e : ℕ) : shiftedIntegralPolynomial w e ≠ 0 := by
  have hlc : w.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hw
  have hlead :
      (shiftedIntegralPolynomial w e).leadingCoeff = w.leadingCoeff := by
    exact shiftedIntegralPolynomial_leadingCoeff w e
  intro hzero
  have hleadZero : (shiftedIntegralPolynomial w e).leadingCoeff = 0 := by
    rw [hzero]
    simp
  rw [hlead] at hleadZero
  exact hlc hleadZero

/-- Rational version of an integral weighted summand. -/
def integralWeightedTermRat (b : ℕ) (w : Polynomial ℤ)
    (S : Set ℕ) (n : ℕ) : ℚ := by
  classical
  exact if n ∈ S then
    (intPolynomialValue w n : ℚ) / (b : ℚ) ^ n
  else 0

theorem integralWeightedTermRat_cast (b : ℕ) (w : Polynomial ℤ)
    (S : Set ℕ) (n : ℕ) :
    (integralWeightedTermRat b w S n : ℝ) =
      integralWeightedTerm b w S n := by
  classical
  by_cases hn : n ∈ S <;>
    simp [integralWeightedTermRat, integralWeightedTerm, hn]

/-- Rational prefix removed before translating the tail. -/
def integralPrefixValue (D : CarrySeries) (e : ℕ) : ℚ :=
  ∑ n ∈ Finset.range e,
    integralWeightedTermRat D.base D.weight D.support n

/-- Rational value of the translated tail. -/
def shiftedSeriesValue (D : CarrySeries) (e : ℕ) : ℚ :=
  (D.base : ℚ) ^ e * (D.value - integralPrefixValue D e)

theorem shifted_integralWeightedTerm (D : CarrySeries) (e n : ℕ) :
    integralWeightedTerm D.base (shiftedIntegralPolynomial D.weight e)
        (shiftedSupport D.support e) n =
      (D.base : ℝ) ^ e *
        integralWeightedTerm D.base D.weight D.support (n + e) := by
  classical
  have hb0 : (D.base : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) D.base_ge_two))
  by_cases hn : n + e ∈ D.support
  · rw [integralWeightedTerm, integralWeightedTerm, if_pos hn]
    have hnShift : n ∈ shiftedSupport D.support e := hn
    rw [if_pos hnShift, shiftedIntegralPolynomial_eval]
    have hpow : (D.base : ℝ) ^ (n + e) =
        (D.base : ℝ) ^ n * (D.base : ℝ) ^ e := by rw [pow_add]
    rw [hpow]
    field_simp
  · have hnShift : n ∉ shiftedSupport D.support e := hn
    simp [integralWeightedTerm, hn, hnShift]

/-- The translated tail is an exact `CarrySeries`. -/
def CarrySeries.shift (D : CarrySeries) (e : ℕ) : CarrySeries where
  base := D.base
  base_ge_two := D.base_ge_two
  weight := shiftedIntegralPolynomial D.weight e
  weight_ne_zero := shiftedIntegralPolynomial_ne_zero D.weight_ne_zero e
  support := shiftedSupport D.support e
  support_infinite := shiftedSupport_infinite D.support_infinite e
  value := shiftedSeriesValue D e
  hasSum := by
    have htail := (hasSum_nat_add_iff'
      (f := integralWeightedTerm D.base D.weight D.support) e).mpr D.hasSum
    have hscaled := htail.mul_left ((D.base : ℝ) ^ e)
    have hprefixCast :
        ((integralPrefixValue D e : ℚ) : ℝ) =
          ∑ n ∈ Finset.range e,
            integralWeightedTerm D.base D.weight D.support n := by
      unfold integralPrefixValue
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      exact integralWeightedTermRat_cast D.base D.weight D.support n
    have hvalueCast :
        ((shiftedSeriesValue D e : ℚ) : ℝ) =
          (D.base : ℝ) ^ e *
            ((D.value : ℝ) -
              ∑ n ∈ Finset.range e,
                integralWeightedTerm D.base D.weight D.support n) := by
      rw [shiftedSeriesValue]
      push_cast
      rw [hprefixCast]
    rw [hvalueCast]
    refine HasSum.congr_fun hscaled ?_
    intro n
    exact shifted_integralWeightedTerm D e n
  positiveFrom := D.positiveFrom
  weight_pos := by
    intro n hn
    rw [shiftedIntegralPolynomial_eval]
    exact D.weight_pos (n + e) (hn.trans (Nat.le_add_right n e))

@[simp]
theorem CarrySeries.shift_base (D : CarrySeries) (e : ℕ) :
    (D.shift e).base = D.base := rfl

@[simp]
theorem CarrySeries.shift_support (D : CarrySeries) (e : ℕ) :
    (D.shift e).support = shiftedSupport D.support e := rfl

@[simp]
theorem CarrySeries.shift_natDegree (D : CarrySeries) (e : ℕ) :
    (D.shift e).weight.natDegree = D.weight.natDegree :=
  shiftedIntegralPolynomial_natDegree D.weight e

/-- Integer obtained by scaling the deleted prefix by `b^e`. -/
def scaledIntegralPrefix (D : CarrySeries) (e : ℕ) : ℤ :=
  ∑ n ∈ Finset.range e,
    intPolynomialValue D.weight n * supportDigitInt D.support n *
      (D.base : ℤ) ^ (e - n)

theorem scaled_integralPrefixValue (D : CarrySeries) (e : ℕ) :
    (D.base : ℚ) ^ e * integralPrefixValue D e =
      (scaledIntegralPrefix D e : ℚ) := by
  classical
  rw [integralPrefixValue, Finset.mul_sum, scaledIntegralPrefix, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hne : n ≤ e := (Finset.mem_range.mp hn).le
  by_cases hsupport : n ∈ D.support
  · rw [integralWeightedTermRat, if_pos hsupport,
      supportDigitInt, if_pos hsupport]
    push_cast
    have hpow : (D.base : ℚ) ^ e =
        (D.base : ℚ) ^ (e - n) * (D.base : ℚ) ^ n := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    have hb0 : (D.base : ℚ) ^ n ≠ 0 := by
      apply pow_ne_zero
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2)
        D.base_ge_two))
    field_simp
  · simp [integralWeightedTermRat, supportDigitInt, hsupport]

theorem shiftedSeriesValue_eq_sub_int (D : CarrySeries) (e : ℕ) :
    shiftedSeriesValue D e =
      D.value * (D.base : ℚ) ^ e - (scaledIntegralPrefix D e : ℤ) := by
  unfold shiftedSeriesValue
  rw [mul_sub, scaled_integralPrefixValue]
  ring

theorem shiftedSeriesValue_den (D : CarrySeries) (e : ℕ) :
    (shiftedSeriesValue D e).den =
      (D.value * (D.base : ℚ) ^ e).den := by
  rw [shiftedSeriesValue_eq_sub_int, Rat.sub_intCast_den]

/-- The `b`-primary part of the rational denominator is removed by one
finite prefix shift.  The surviving denominator divides the explicit fixed
coprime part `Q`. -/
theorem CarrySeries.exists_coprime_shift (D : CarrySeries) :
    ∃ e Q : ℕ, 0 < Q ∧ Nat.Coprime Q D.base ∧
      (D.shift e).denominator ∣ Q := by
  obtain ⟨e, Q, hQ, hcoprime, hdiv⟩ :=
    exists_coprime_denominator_after_prefix D.value D.base_ge_two
  refine ⟨e, Q, hQ, hcoprime, ?_⟩
  change (shiftedSeriesValue D e).den ∣ Q
  rw [shiftedSeriesValue_den]
  exact hdiv

theorem CarrySeries.shift_denominator_coprime (D : CarrySeries) :
    ∃ e : ℕ, Nat.Coprime (D.shift e).denominator D.base := by
  obtain ⟨e, Q, hQ, hcoprime, hdiv⟩ := D.exists_coprime_shift
  exact ⟨e, Nat.Coprime.of_dvd_left hdiv hcoprime⟩

/-- Translating a window and the tail support by the same finite offset
preserves its cardinality exactly. -/
theorem windowCount_shiftedSupport (S : Set ℕ) (e N W : ℕ) :
    windowCount (shiftedSupport S e) N W = windowCount S (N + e) W := by
  classical
  unfold windowCount
  have hmap :
      (((Finset.Ioc N (N + W)).filter fun n => n ∈ shiftedSupport S e).map
          (addRightEmbedding e)) =
        (Finset.Ioc (N + e) (N + e + W)).filter fun n => n ∈ S := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_Ioc,
      addRightEmbedding_apply]
    constructor
    · rintro ⟨a, ⟨⟨haN, haW⟩, haS⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, haS⟩
    · rintro ⟨⟨hnN, hnW⟩, hnS⟩
      refine ⟨n - e, ?_, by omega⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      show n - e + e ∈ S
      rw [Nat.sub_add_cancel (by omega : e ≤ n)]
      exact hnS
  have hcard := congrArg Finset.card hmap
  simpa using hcard

/-- A uniform density estimate on a finitely translated tail gives one on the
original support.  The harmless factor `1/2` is explicit and the new cutoff
absorbs the translation uniformly over every admissible width. -/
theorem uniformlyEventually_windowCount_of_shiftedSupport
    {S : Set ℕ} (e : ℕ) {θ c : ℝ}
    (hθ : 0 < θ) (hθone : θ ≤ 1) (hc : 0 < c)
    (hshift : UniformlyEventually θ fun N W =>
      c * W ≤ windowCount (shiftedSupport S e) N W) :
    UniformlyEventually θ fun N W =>
      (c / 2) * W ≤ windowCount S N W := by
  obtain ⟨N₀, hN₀⟩ := hshift
  refine ⟨max (N₀ + e) (2 * e + 1), ?_⟩
  intro N W hN hwindow
  have heN : e ≤ N := by omega
  let N' := N - e
  let W' := min W N'
  have hN'eq : N' + e = N := by
    dsimp only [N']
    exact Nat.sub_add_cancel heN
  have hN'pos : 0 < N' := by
    dsimp only [N']
    omega
  have hN₀N' : N₀ ≤ N' := by
    dsimp only [N']
    omega
  have hW'pos : 0 < W' := by
    dsimp only [W']
    exact lt_min (admissibleWindow_width_pos hwindow) hN'pos
  have hN'leN : N' ≤ N := by
    dsimp only [N']
    omega
  have hrpowW : Real.rpow (N' : ℝ) θ ≤ (W : ℝ) := by
    have hcast : (N' : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN'leN
    exact (Real.rpow_le_rpow (by positivity) hcast hθ.le).trans hwindow.2.1
  have hrpowN' : Real.rpow (N' : ℝ) θ ≤ (N' : ℝ) := by
    apply Real.rpow_le_self_of_one_le
    · exact_mod_cast hN'pos
    · exact hθone
  have hW'admissible : AdmissibleWindow θ N' W' := by
    refine ⟨hN'pos, ?_, min_le_right _ _⟩
    simpa only [W', Nat.cast_min] using le_min hrpowW hrpowN'
  have hshiftCount := hN₀ N' W' hN₀N' hW'admissible
  have htranslate :
      windowCount (shiftedSupport S e) N' W' = windowCount S N W' := by
    rw [windowCount_shiftedSupport, hN'eq]
  change c * (W' : ℝ) ≤
    (windowCount (shiftedSupport S e) N' W' : ℝ) at hshiftCount
  rw [htranslate] at hshiftCount
  have hW'leW : W' ≤ W := by exact min_le_left _ _
  have hcountMono := windowCount_mono_width S N hW'leW
  have hNtwoE : 2 * e ≤ N := by omega
  have hWleN : W ≤ N := hwindow.2.2
  have hhalf : (W : ℝ) / 2 ≤ (W' : ℝ) := by
    have hNat : W ≤ 2 * W' := by
      dsimp only [W']
      by_cases hWN : W ≤ N'
      · rw [min_eq_left hWN]
        omega
      · rw [min_eq_right (Nat.le_of_not_ge hWN)]
        dsimp only [N']
        omega
    have hNatReal : (W : ℝ) ≤ 2 * (W' : ℝ) := by
      exact_mod_cast hNat
    linarith
  have hscaled : (c / 2) * (W : ℝ) ≤ c * (W' : ℝ) := by
    calc
      (c / 2) * (W : ℝ) = c * ((W : ℝ) / 2) := by ring
      _ ≤ c * (W' : ℝ) := mul_le_mul_of_nonneg_left hhalf hc.le
  exact hscaled.trans (hshiftCount.trans (by exact_mod_cast hcountMono))

/-! ## Canonical nonrare prefix graphs -/

/-- Realized locking prefixes with more than `d+1` occurrences.  This is the
literal complement of the manuscript's rare class inside the realized
prefix family. -/
def canonicalNonrarePrefixes (D : CarrySeries)
    (N W m bound : ℕ) : Finset Erdos260.GapWord :=
  (realizedLockingPrefixes D.positiveEnumeration N W m bound).filter fun pfx =>
    D.weight.natDegree + 1 <
      (realizedPrefixIndices D N W m bound pfx).card

@[simp]
theorem mem_canonicalNonrarePrefixes_iff (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord} :
    pfx ∈ canonicalNonrarePrefixes D N W m bound ↔
      pfx ∈ realizedLockingPrefixes D.positiveEnumeration N W m bound ∧
        D.weight.natDegree + 1 <
          (realizedPrefixIndices D N W m bound pfx).card := by
  simp [canonicalNonrarePrefixes]

/-- A canonical nonrare prefix at one finite window scale. -/
abbrev CanonicalNonrarePrefix (D : CarrySeries)
    (N W m bound : ℕ) :=
  ↑(canonicalNonrarePrefixes D N W m bound)

/-- The graph selected once for a canonical nonrare prefix.  Its definition
depends only on the proved geometric scale data and uses the explicit
locking threshold, never an assumed graph. -/
noncomputable def canonicalLockedGraph (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N)) :
    PolynomialGraph D.weight.natDegree := by
  apply Classical.choose
  apply lockedGraph_of_nonrarePrefix_explicit D hgeom hW hscale pfx.1
  · exact (mem_canonicalNonrarePrefixes_iff D).mp pfx.2 |>.2.le
  · exact hpositiveFrom

theorem canonicalLockedGraph_den_le (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N)) :
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx).denominator ≤
      (W + lockingThreshold D N + cap) ^
        vandermondeExponent D.weight.natDegree := by
  exact (Classical.choose_spec
    (lockedGraph_of_nonrarePrefix_explicit D hgeom hW hscale pfx.1
      ((mem_canonicalNonrarePrefixes_iff D).mp pfx.2 |>.2.le)
      hpositiveFrom)).1

/-- Uniform upper bound for the normalized denominator of every canonical
locked graph in one window. -/
def globalActualInteriorStateDenominatorCap (D : CarrySeries)
    (N W cap : ℕ) : ℕ :=
  (W + lockingThreshold D N + cap) ^
      vandermondeExponent D.weight.natDegree *
    D.denominator * (D.weight.coeff D.weight.natDegree).natAbs

/-- Uniform upper bound for every stabilized logarithmic block scale. -/
def globalActualInteriorBlockScaleCap (D : CarrySeries)
    (N W cap : ℕ) : ℕ :=
  logarithmicBlockScale D.base 4
    (globalActualInteriorStateDenominatorCap D N W cap)

/-- A uniform stabilization threshold for every canonical locked graph in one
window.  Besides denominator absorption it includes the complete boundary
margin needed by the retained-block cover. -/
def globalActualInteriorThreshold (D : CarrySeries)
    (N W m cap reserve : ℕ) : ℕ :=
  Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) +
    2 * cap + 24 * globalActualInteriorBlockScaleCap D N W cap +
      reserve * m

/-- Canonical locked states satisfy the common denominator cap. -/
theorem canonicalLockedTopState_den_le_cap (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N)) :
    (PolynomialGraph.normalizedTopState
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
      D.denominator D.weight).den ≤
        globalActualInteriorStateDenominatorCap D N W cap := by
  exact InteriorNumeratorOrbit.normalizedTopState_den_le_of_graph_den_le
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
    (canonicalLockedGraph_den_le D hgeom hW hscale hpositiveFrom pfx)
    D.denominator_pos D.weight hw

/-- The uniform threshold really dominates every source-specific normalized
denominator threshold. -/
theorem globalActualInteriorThreshold_covers (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (reserve : ℕ)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N)) :
    Nat.log 2 (PolynomialGraph.normalizedTopState
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        D.denominator D.weight).den + cap ≤
      globalActualInteriorThreshold D N W m cap reserve := by
  have hden := canonicalLockedTopState_den_le_cap
    D hgeom hW hscale hpositiveFrom hw pfx
  have hlog : Nat.log 2 (PolynomialGraph.normalizedTopState
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        D.denominator D.weight).den ≤
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) := by
    exact Nat.log_mono_right hden
  unfold globalActualInteriorThreshold
  omega

theorem canonicalLockedGraph_fit (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N)) :
    ∀ x ∈ realizedPrefixAnchors D N W m (lockingThreshold D N) pfx.1,
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx).poly.eval
          (x + Erdos260.GapWord.span pfx.1 : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx.1) : ℚ) := by
  exact (Classical.choose_spec
    (lockedGraph_of_nonrarePrefix_explicit D hgeom hW hscale pfx.1
      ((mem_canonicalNonrarePrefixes_iff D).mp pfx.2 |>.2.le)
      hpositiveFrom)).2

/-! ## Global retained interior sources -/

/-- All genuine retained block occurrences over all canonical nonrare
prefixes.  The graph is the canonical choice proved above, so it is not a
field that a caller can choose independently. -/
abbrev GlobalActualInteriorBlockSource (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) :=
  Σ pfx : CanonicalNonrarePrefix
      D N W m (lockingThreshold D N),
    CanonicalActualInteriorBlockSource D N W m (lockingThreshold D N)
      pfx.1 (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
      threshold

/-- Every actual source built at the canonical threshold has its stabilized
block scale below the common window cap. -/
theorem globalActualInteriorBlockScale_le_cap (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (reserve : ℕ)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    actualInteriorBlockScale D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        (globalActualInteriorThreshold D N W m cap reserve) source.2.anchor ≤
      globalActualInteriorBlockScaleCap D N W cap := by
  apply actualInteriorBlockScale_le_of_state_den_le
    D hgeom source.1.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
  · exact globalActualInteriorThreshold_covers
      D hgeom hW hscale hpositiveFrom hw reserve source.1
  · exact canonicalLockedTopState_den_le_cap
      D hgeom hW hscale hpositiveFrom hw source.1

/-- The canonical threshold includes the stronger margin required by the
retained-block cover, uniformly for every actual source. -/
theorem globalActualInteriorThreshold_covers_retained (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (reserve : ℕ)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    Nat.log 2 (PolynomialGraph.normalizedTopState
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        D.denominator D.weight).den +
      2 * cap +
        24 * actualInteriorBlockScale D source.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
          (globalActualInteriorThreshold D N W m cap reserve) source.2.anchor ≤
      globalActualInteriorThreshold D N W m cap reserve := by
  have hlog : Nat.log 2 (PolynomialGraph.normalizedTopState
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        D.denominator D.weight).den ≤
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) :=
    Nat.log_mono_right (canonicalLockedTopState_den_le_cap
      D hgeom hW hscale hpositiveFrom hw source.1)
  have hell := globalActualInteriorBlockScale_le_cap D hw reserve source
  conv_rhs => rw [globalActualInteriorThreshold]
  omega

/-- The reserve term in the canonical threshold is available uniformly after
denominator absorption. -/
theorem globalActualInteriorThreshold_covers_reserve (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N)) :
    Nat.log 2 (PolynomialGraph.normalizedTopState
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        D.denominator D.weight).den +
      2 * cap + reserve * m ≤
        globalActualInteriorThreshold D N W m cap reserve := by
  have hlog : Nat.log 2 (PolynomialGraph.normalizedTopState
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        D.denominator D.weight).den ≤
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) :=
    Nat.log_mono_right (canonicalLockedTopState_den_le_cap
      D hgeom hW hscale hpositiveFrom hw pfx)
  conv_rhs => rw [globalActualInteriorThreshold]
  omega

noncomputable instance instDecidableEqGlobalActualInteriorBlockSource
    (D : CarrySeries) {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) :
    DecidableEq (GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :=
  Classical.decEq _

/-- Endpoint coordinate and within-window offset for a global actual source. -/
noncomputable def globalActualInteriorBlockSourceMap (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ × ℕ :=
  actualInteriorBlockSourceMap D source.2

/-- The source map is genuinely injective across different locked-prefix
fibres.  Equal endpoint and offset first recover the same window anchor; the
anchor's canonical locking prefix then recovers the outer sigma component,
after which the already proved local source injection applies. -/
theorem globalActualInteriorBlockSourceMap_injective (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ} :
    Function.Injective
      (globalActualInteriorBlockSourceMap D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) (threshold := threshold)) := by
  classical
  rintro ⟨leftPrefix, left⟩ ⟨rightPrefix, right⟩ hmap
  let leftEndpoint := actualInteriorBlockSourceEndpointIndex D left
  let rightEndpoint := actualInteriorBlockSourceEndpointIndex D right
  change (D.positiveEnumeration.a leftEndpoint,
      leftEndpoint - left.anchor.1) =
    (D.positiveEnumeration.a rightEndpoint,
      rightEndpoint - right.anchor.1) at hmap
  have hendpoint : leftEndpoint = rightEndpoint :=
    D.positiveEnumeration.strictMono.injective (Prod.mk.inj hmap).1
  have hleftStart : left.anchor.1 ≤ leftEndpoint :=
    actualInteriorBlockEndpointIndex_start_le D leftPrefix.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom leftPrefix)
      threshold _ left.anchor left.blockIndex
  have hrightStart : right.anchor.1 ≤ rightEndpoint :=
    actualInteriorBlockEndpointIndex_start_le D rightPrefix.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom rightPrefix)
      threshold _ right.anchor right.blockIndex
  have hanchorVal : left.anchor.1 = right.anchor.1 := by
    have hoffset := (Prod.mk.inj hmap).2
    rw [hendpoint] at hoffset hleftStart
    omega
  have hleftPrefixValue :
      lockingPrefix D.positiveEnumeration left.anchor.1 m
          (lockingThreshold D N) = leftPrefix.1 := by
    exact (Finset.mem_filter.mp
      ((Finset.mem_filter.mp left.anchor.2).1)).2
  have hrightPrefixValue :
      lockingPrefix D.positiveEnumeration right.anchor.1 m
          (lockingThreshold D N) = rightPrefix.1 := by
    exact (Finset.mem_filter.mp
      ((Finset.mem_filter.mp right.anchor.2).1)).2
  have hprefixVal : leftPrefix.1 = rightPrefix.1 := by
    rw [← hleftPrefixValue, ← hrightPrefixValue, hanchorVal]
  have hprefix : leftPrefix = rightPrefix := Subtype.ext hprefixVal
  subst rightPrefix
  have hlocal : left = right := by
    apply canonicalActualInteriorBlockSourceMap_injective D
    simpa only [actualInteriorBlockSourceMap, leftEndpoint,
      rightEndpoint] using hmap
  subst right
  rfl

/-- Enumeration index of the retained block endpoint of a global source. -/
noncomputable def globalActualInteriorEndpointIndex (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ :=
  actualInteriorBlockSourceEndpointIndex D source.2

/-- Actual support coordinate of a global retained block endpoint. -/
noncomputable def globalActualInteriorEndpoint (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ :=
  D.positiveEnumeration.a (globalActualInteriorEndpointIndex D source)

/-- Proof-bearing within-window endpoint offset. -/
noncomputable def globalActualInteriorOffset (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : Fin (m + 1) :=
  ⟨globalActualInteriorEndpointIndex D source - source.2.anchor.1,
    Nat.lt_succ_iff.mpr
      (canonicalActualInteriorBlockSource_offset_le D source.2)⟩

theorem globalActualInteriorEndpointOffset_injective (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ} :
    Function.Injective fun source :
        GlobalActualInteriorBlockSource D hgeom hW hscale
          hpositiveFrom threshold =>
      (globalActualInteriorEndpoint D source,
        (globalActualInteriorOffset D source : ℕ)) := by
  change Function.Injective
    (globalActualInteriorBlockSourceMap D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) (threshold := threshold))
  exact globalActualInteriorBlockSourceMap_injective D

/-- A source survives the explicit common-continuation cutoff. -/
def GlobalActualInteriorBlockSource.Deep (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) (F : ℕ) : Prop :=
  source.2.Deep D F

/-- Finite family of all deep global retained sources. -/
noncomputable def globalActualInteriorDeepSources (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} (threshold F : ℕ) :
    Finset (GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) := by
  classical
  exact Finset.univ.filter fun source => source.Deep D F

/-- Exact finite code used by the global interior census: retained block
word, denominator band, and mean-gap band. -/
abbrev GlobalActualInteriorCode := Erdos260.GapWord × ℕ × ℕ

noncomputable def globalActualInteriorBlockWord (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : Erdos260.GapWord :=
  canonicalActualInteriorBlockWord D source.2

noncomputable def globalActualInteriorDenominatorBand (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ :=
  dyadicFloorBand (actualInteriorDenominator D source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    threshold source.2.anchor)

noncomputable def globalActualInteriorMeanGapBand (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ :=
  actualInteriorMeanGapBand D source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    threshold source.2.anchor

/-- Every source selected with the reserve-augmented canonical threshold keeps
more than `reserve * m` units of stabilized interior span. -/
theorem globalActualInteriorStabilizedSpan_gt_reserve_mul (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    reserve * m < Erdos260.GapWord.span
      (actualStabilizedInteriorWord D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        (globalActualInteriorThreshold D N W m cap reserve)
        source.2.anchor) := by
  exact actualStabilizedInteriorWord_span_gt
    D hgeom source.1.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
      (globalActualInteriorThreshold D N W m cap reserve)
      (globalActualInteriorThreshold_covers_reserve
        D hw source.1) source.2.anchor

/-- Consequently every realized mean-gap band is uniformly large: the exact
dyadic convention gives `reserve < 2Z`. -/
theorem globalActualInteriorReserve_lt_two_mul_meanGapBand (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    reserve < 2 * globalActualInteriorMeanGapBand D source := by
  let word := actualStabilizedInteriorWord D source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    (globalActualInteriorThreshold D N W m cap reserve) source.2.anchor
  have hspan : reserve * m < Erdos260.GapWord.span word := by
    simpa only [word] using
      globalActualInteriorStabilizedSpan_gt_reserve_mul D hw source
  have hlength : word.length ≤ m := by
    simpa only [word] using actualStabilizedInteriorWord_length_le
      D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        (globalActualInteriorThreshold D N W m cap reserve) source.2.anchor
  have hspanPos : 0 < Erdos260.GapWord.span word :=
    (Nat.zero_le (reserve * m)).trans_lt hspan
  have hwordNe : word ≠ [] := by
    intro hnil
    rw [hnil] at hspanPos
    simp [Erdos260.GapWord.span] at hspanPos
  have hlengthPos : 0 < word.length := List.length_pos_iff.mpr hwordNe
  have hmul : reserve * word.length < Erdos260.GapWord.span word :=
    (Nat.mul_le_mul_left reserve hlength).trans_lt hspan
  have hmean : reserve ≤ Erdos260.GapWord.span word / word.length :=
    (Nat.le_div_iff_mul_le hlengthPos).2 hmul.le
  have hband := dyadicFloorBand_lt_two_mul
    (Erdos260.GapWord.span word / word.length)
  simpa only [globalActualInteriorMeanGapBand,
    actualInteriorMeanGapBand, meanGapBand, word] using hmean.trans_lt hband

/-- The orbit recurrence couples the two dyadic bands: the base raised to the
mean-gap band is strictly smaller than four times the denominator band. -/
theorem globalActualInteriorMeanGapBand_base_pow_lt_four_mul_denominatorBand
    (D : CarrySeries) {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    D.base ^ globalActualInteriorMeanGapBand D source <
      4 * globalActualInteriorDenominatorBand D source := by
  let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let word := actualStabilizedInteriorWord D source.1.1 G threshold source.2.anchor
  let q := actualInteriorDenominator D source.1.1 G threshold source.2.anchor
  let Z := globalActualInteriorMeanGapBand D source
  let Dband := globalActualInteriorDenominatorBand D source
  let O := actualInteriorOrbit D hw hgeom source.1.1 G threshold
    (globalActualInteriorThreshold_covers
      D hgeom hW hscale hpositiveFrom hw reserve source.1) source.2.anchor
  have hspanPos : 0 < Erdos260.GapWord.span word := by
    have hspan := globalActualInteriorStabilizedSpan_gt_reserve_mul D hw source
    simpa only [word, G, threshold] using (Nat.zero_le (reserve * m)).trans_lt hspan
  have hwordNe : word ≠ [] := by
    intro hnil
    rw [hnil] at hspanPos
    simp [Erdos260.GapWord.span] at hspanPos
  have hlengthPos : 0 < word.length := List.length_pos_iff.mpr hwordNe
  have hpositive : Erdos260.GapWord.Positive word := by
    simpa only [word, G, threshold] using
      actualStabilizedInteriorWord_positive D source.1.1 G threshold source.2.anchor
  have hlengthSpan : word.length ≤ Erdos260.GapWord.span word :=
    List.length_le_sum_of_one_le word hpositive
  have hZle : Z ≤ Erdos260.GapWord.span word / word.length := by
    simpa only [Z, globalActualInteriorMeanGapBand, G, threshold, word,
      actualInteriorMeanGapBand] using
        (meanGapBand_bounds hlengthPos hlengthSpan).1
  have hZleReal : (Z : ℝ) ≤
      (Erdos260.GapWord.span word : ℝ) / word.length := by
    have hcast : (Z : ℝ) ≤
        ((Erdos260.GapWord.span word / word.length : ℕ) : ℝ) := by
      exact_mod_cast hZle
    exact hcast.trans Nat.cast_div_le
  have hbaseOne : (1 : ℝ) ≤ D.base := by
    have hbasePos : 0 < D.base :=
      lt_of_lt_of_le (by decide : 0 < 2) D.base_ge_two
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hbasePos.ne')
  have hpowMono : Real.rpow (D.base : ℝ) Z ≤
      Real.rpow (D.base : ℝ)
        ((Erdos260.GapWord.span word : ℝ) / word.length) :=
    Real.rpow_le_rpow_of_exponent_le hbaseOne hZleReal
  have hmean : Real.rpow (D.base : ℝ)
        ((Erdos260.GapWord.span word : ℝ) / word.length) ≤ 2 * q := by
    have hOgaps : O.gaps = word := by rfl
    have hraw := O.meanGap_rpow_le (by rw [hOgaps]; exact hwordNe)
    rw [hOgaps] at hraw
    simpa only [O, q, actualInteriorDenominator] using hraw
  have hqband : q < 2 * Dband := by
    simpa only [q, Dband, globalActualInteriorDenominatorBand, G, threshold] using
      (actualInteriorDenominator_band D hw hgeom source.1.1 G threshold
        (globalActualInteriorThreshold_covers
          D hgeom hW hscale hpositiveFrom hw reserve source.1)
        source.2.anchor).2
  have hpowReal : ((D.base ^ Z : ℕ) : ℝ) < (4 * Dband : ℕ) := by
    calc
      ((D.base ^ Z : ℕ) : ℝ) = Real.rpow (D.base : ℝ) Z := by
        push_cast
        exact (Real.rpow_natCast D.base Z).symm
      _ ≤ Real.rpow (D.base : ℝ)
          ((Erdos260.GapWord.span word : ℝ) / word.length) := hpowMono
      _ ≤ 2 * q := hmean
      _ < ((4 * Dband : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * q < 4 * Dband)
  exact_mod_cast hpowReal

noncomputable def globalActualInteriorCode (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : GlobalActualInteriorCode :=
  (globalActualInteriorBlockWord D source,
    globalActualInteriorDenominatorBand D source,
    globalActualInteriorMeanGapBand D source)

/-- Exact polynomial/code key of a retained source. -/
abbrev GlobalActualInteriorGraphKey :=
  Polynomial ℚ × GlobalActualInteriorCode

noncomputable def globalActualInteriorGraphKey (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : GlobalActualInteriorGraphKey :=
  ((canonicalActualInteriorBlockEndGraph D source.2).poly,
    globalActualInteriorCode D source)

/-- Exponent of the dyadic mean-gap band attached to a retained source. -/
noncomputable def globalActualInteriorMeanGapExponent (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ :=
  Nat.log 2
    (Erdos260.GapWord.span
        (actualStabilizedInteriorWord D source.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
          threshold source.2.anchor) /
      (actualStabilizedInteriorWord D source.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
          threshold source.2.anchor).length)

/-- Exponent of the dyadic denominator band attached to a retained source. -/
noncomputable def globalActualInteriorDenominatorExponent (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ :=
  Nat.log 2 (actualInteriorDenominator D source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    threshold source.2.anchor)

theorem globalActualInteriorDenominatorBand_eq_pow_exponent (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :
    globalActualInteriorDenominatorBand D source =
      2 ^ globalActualInteriorDenominatorExponent D source := by
  rfl

/-- At the canonical threshold, the denominator-band exponent lies in the
finite range determined by the window-level state denominator cap. -/
theorem globalActualInteriorDenominatorExponent_le (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    globalActualInteriorDenominatorExponent D source ≤
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) := by
  apply Nat.log_mono_right
  exact (actualInteriorDenominator_le_initial D hgeom source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    (globalActualInteriorThreshold D N W m cap reserve)
    (globalActualInteriorThreshold_covers
      D hgeom hW hscale hpositiveFrom hw reserve source.1)
    source.2.anchor).trans
      (canonicalLockedTopState_den_le_cap
        D hgeom hW hscale hpositiveFrom hw source.1)

theorem globalActualInteriorMeanGapBand_eq_pow_exponent (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :
    globalActualInteriorMeanGapBand D source =
      2 ^ globalActualInteriorMeanGapExponent D source := by
  rfl

/-- A retained block position is one of the next `m+1` enumeration slots. -/
theorem globalActualInteriorBlockPosition_le (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :
    source.2.blockIndex.1 ≤ m := by
  let word := actualStabilizedInteriorWord D source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    threshold source.2.anchor
  let ell := actualInteriorBlockScale D source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    threshold source.2.anchor
  have hblocks : (completedGreedyBlocks word ell).length ≤ word.length :=
    completedGreedyBlocks_length_le word ell
      (actualInteriorBlockScale_pos D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        threshold source.2.anchor)
  have hword : word.length ≤ m := by
    simpa only [word] using actualStabilizedInteriorWord_length_le
      D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        threshold source.2.anchor
  have hindex : source.2.blockIndex.1 <
      (completedGreedyBlocks word ell).length := source.2.blockIndex.isLt
  omega

/-- The exponent of every realized mean-gap band is at most `log₂ cap`. -/
theorem globalActualInteriorMeanGapExponent_le (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :
    globalActualInteriorMeanGapExponent D source ≤ Nat.log 2 cap := by
  let word := actualStabilizedInteriorWord D source.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
    threshold source.2.anchor
  have hgap : ∀ g ∈ word, g ≤ cap := by
    simpa only [word] using actualStabilizedInteriorWord_gap_le
      D hgeom source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        threshold source.2.anchor
  have hsum : word.sum ≤ word.length * cap := by
    simpa using word.sum_le_card_nsmul cap hgap
  have hmean : word.sum / word.length ≤ cap :=
    Nat.div_le_of_le_mul hsum
  apply Nat.log_mono_right
  simpa only [globalActualInteriorMeanGapExponent,
    Erdos260.GapWord.span, word] using hmean

/-- Manuscript cell label: nonrare prefix, completed-block position, and
dyadic mean-gap band exponent.  All three components are proof-bounded. -/
abbrev GlobalActualInteriorCell (D : CarrySeries)
    (N W m cap : ℕ) :=
  (CanonicalNonrarePrefix D N W m (lockingThreshold D N) × Fin (m + 1)) ×
    Fin (Nat.log 2 cap + 1)

noncomputable def globalActualInteriorCell (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : GlobalActualInteriorCell D N W m cap :=
  ((source.1, ⟨source.2.blockIndex.1,
      Nat.lt_succ_iff.mpr (globalActualInteriorBlockPosition_le D source)⟩),
    ⟨globalActualInteriorMeanGapExponent D source,
      Nat.lt_succ_iff.mpr
        (globalActualInteriorMeanGapExponent_le D source)⟩)

/-- The exact block-end graph/code key factors through the manuscript cell
label.  In particular no exact graph is stored as a cell assumption. -/
theorem globalActualInteriorGraphKey_eq_of_cell_eq (D : CarrySeries)
    {N W m cap threshold : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (left right : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hcell : globalActualInteriorCell D left =
      globalActualInteriorCell D right) :
    globalActualInteriorGraphKey D left =
      globalActualInteriorGraphKey D right := by
  rcases left with ⟨leftPrefix, left⟩
  rcases right with ⟨rightPrefix, right⟩
  have hprefix : leftPrefix = rightPrefix := by
    have h := congrArg
      (fun cell : GlobalActualInteriorCell D N W m cap => cell.1.1) hcell
    simpa only [globalActualInteriorCell] using h
  have hindex : left.blockIndex.1 = right.blockIndex.1 := by
    have h := congrArg
      (fun cell : GlobalActualInteriorCell D N W m cap =>
        (cell.1.2 : ℕ)) hcell
    simpa only [globalActualInteriorCell] using h
  have hexponent :
      globalActualInteriorMeanGapExponent D ⟨leftPrefix, left⟩ =
        globalActualInteriorMeanGapExponent D ⟨rightPrefix, right⟩ := by
    have h := congrArg
      (fun cell : GlobalActualInteriorCell D N W m cap =>
        (cell.2 : ℕ)) hcell
    simpa only [globalActualInteriorCell] using h
  subst rightPrefix
  have hword := canonicalActualInteriorBlockWord_eq_of_position
    D hgeom (hthreshold leftPrefix) left right hindex
  have hgraph := canonicalActualInteriorBlockEndGraph_eq_of_position
    D hgeom (hthreshold leftPrefix) left right hindex
  have hden := actualInteriorDenominator_eq
    D hgeom leftPrefix.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom leftPrefix)
      threshold (hthreshold leftPrefix) left.anchor right.anchor
  have hband :
      globalActualInteriorDenominatorBand D ⟨leftPrefix, left⟩ =
        globalActualInteriorDenominatorBand D ⟨leftPrefix, right⟩ := by
    simpa only [globalActualInteriorDenominatorBand] using
      congrArg dyadicFloorBand hden
  have hmean :
      globalActualInteriorMeanGapBand D ⟨leftPrefix, left⟩ =
        globalActualInteriorMeanGapBand D ⟨leftPrefix, right⟩ := by
    rw [globalActualInteriorMeanGapBand_eq_pow_exponent,
      globalActualInteriorMeanGapBand_eq_pow_exponent, hexponent]
  have hcode : globalActualInteriorCode D ⟨leftPrefix, left⟩ =
      globalActualInteriorCode D ⟨leftPrefix, right⟩ := by
    unfold globalActualInteriorCode
    apply Prod.ext
    · simpa only [globalActualInteriorBlockWord] using hword
    · exact Prod.ext hband hmean
  exact Prod.ext (congrArg PolynomialGraph.poly hgraph) hcode

/-- Realized manuscript cells among the deep retained source family. -/
noncomputable def globalActualInteriorCells (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} (threshold F : ℕ) :
    Finset (GlobalActualInteriorCell D N W m cap) :=
  (globalActualInteriorDeepSources D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) threshold F).image
    (globalActualInteriorCell D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom))

/-- Exact finite form of `eq:cellcount` for the actual global sources. -/
theorem globalActualInteriorCells_card_le (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} :
    (globalActualInteriorCells D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F).card ≤
      (canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card *
        (m + 1) * (Nat.log 2 cap + 1) := by
  have hcard := Finset.card_le_univ
    (globalActualInteriorCells D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F)
  simpa only [GlobalActualInteriorCell, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_fin] using hcard

/-- Hence the number of actual exact graph keys obeys the same cell count. -/
theorem globalActualInteriorGraphKeys_card_le (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold) :
    (interiorCensusGraphKeys
        (globalActualInteriorDeepSources D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) threshold F)
        (globalActualInteriorGraphKey D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom))).card ≤
      (canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card *
        (m + 1) * (Nat.log 2 cap + 1) := by
  have hfactor :
      (interiorCensusGraphKeys
        (globalActualInteriorDeepSources D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) threshold F)
        (globalActualInteriorGraphKey D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom))).card ≤
      (globalActualInteriorCells D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F).card := by
    apply image_card_le_image_card_of_factors
    intro left _hleft right _hright hcell
    exact globalActualInteriorGraphKey_eq_of_cell_eq
      D hthreshold left right hcell
  exact hfactor.trans (globalActualInteriorCells_card_le D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom))

/-- Span charged to one actual retained source. -/
noncomputable def globalActualInteriorBlockSpan (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : ℕ :=
  canonicalActualInteriorBlockSourceSpan D source.2

/-- Every source span is bounded by the explicit scale encoded in its
denominator-band component. -/
theorem globalActualInteriorBlockSpan_le (D : CarrySeries)
    {N W m cap threshold : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :
    globalActualInteriorBlockSpan D source ≤
      4 * logarithmicBlockScale D.base 4
        (globalActualInteriorDenominatorBand D source) := by
  have hmem := canonicalActualInteriorBlockWord_mem_retainedWords
    D hw hgeom (hthreshold source.1) source.2
  have hbounds := (mem_retainedBlockWords_iff.mp hmem).2.2.1
  change Erdos260.GapWord.span
      (canonicalActualInteriorBlockWord D source.2) ≤
    4 * logarithmicBlockScale D.base 4
      (dyadicFloorBand (actualInteriorDenominator D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        threshold source.2.anchor))
  exact hbounds

/-- Every genuine retained global block automatically satisfies the strict
Farey-separation inequality; this is no longer an asymptotic assumption. -/
theorem globalActualInterior_short_separation (D : CarrySeries)
    {N W m cap threshold : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :
    1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
        Erdos260.GapWord.span (globalActualInteriorBlockWord D source)) <
      1 / (4 * (globalActualInteriorDenominatorBand D source : ℝ) ^ 2) := by
  have hmem := canonicalActualInteriorBlockWord_mem_retainedWords
    D hw hgeom (hthreshold source.1) source.2
  simpa only [globalActualInteriorBlockWord,
    globalActualInteriorDenominatorBand, actualInteriorBlockScale] using
    retainedBlockWord_short_separation D.base_ge_two
      (dyadicFloorBand_pos
        (actualInteriorDenominator D source.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
          threshold source.2.anchor))
      (canonicalActualInteriorBlockWord D source.2) hmem

/-- Reindexing the dependent global source family recovers exactly the sum
of the canonical retained masses of all nonrare prefix fibres. -/
theorem globalActualInteriorBlockSpan_sum (D : CarrySeries)
    {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    (∑ source : GlobalActualInteriorBlockSource D hgeom hW hscale
        hpositiveFrom threshold,
      globalActualInteriorBlockSpan D source) =
      ∑ pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N),
        actualInteriorRetainedMass D (N := N) (W := W) (m := m)
          (bound := lockingThreshold D N) pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro pfx _hpfx
  simpa only [globalActualInteriorBlockSpan] using
    canonicalActualInteriorBlockSourceSpan_sum D pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx) threshold

/-- Filtering the dependent global source family by the genuine deep
continuation predicate recovers exactly the sum of the deep retained masses
of the canonical nonrare prefix fibres. -/
theorem globalActualInteriorDeepBlockSpan_sum (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    (∑ source ∈ globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F,
      globalActualInteriorBlockSpan D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) source) =
      ∑ pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N),
        actualInteriorDeepRetainedMass D
          (N := N) (W := W) (m := m)
          (bound := lockingThreshold D N) pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold F := by
  classical
  unfold globalActualInteriorDeepSources
  rw [Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro pfx _hpfx
  rfl

/-- All genuinely interior-eligible window indices, retaining the canonical
nonrare prefix fibre to which each index belongs. -/
abbrev GlobalActualInteriorEligibleIndex (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) :=
  Σ pfx : CanonicalNonrarePrefix
      D N W m (lockingThreshold D N),
    ↥(interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx) threshold)

/-- Forgetting the prefix fibre sends every globally eligible index back to
the original finite window. -/
noncomputable def globalActualInteriorEligibleIndexToWindow (D : CarrySeries)
    {N W m cap threshold : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (source : GlobalActualInteriorEligibleIndex D hgeom hW hscale
      hpositiveFrom threshold) :
    ↥(windowIndices D.positiveEnumeration N W) :=
  ⟨source.2.1, by
    have heligible := (Finset.mem_filter.mp source.2.2).1
    have hrealized := (Finset.mem_filter.mp heligible).1
    exact (Finset.mem_filter.mp hrealized).1⟩

/-- Prefix fibres are disjoint on actual window indices: the index itself
determines its canonical locking prefix. -/
theorem globalActualInteriorEligibleIndexToWindow_injective (D : CarrySeries)
    {N W m cap threshold : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} :
    Function.Injective
      (globalActualInteriorEligibleIndexToWindow D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) (threshold := threshold)) := by
  rintro ⟨leftPrefix, leftIndex⟩ ⟨rightPrefix, rightIndex⟩ hmap
  have hindexValue : leftIndex.1 = rightIndex.1 :=
    congrArg Subtype.val hmap
  have hleftRealized : leftIndex.1 ∈ realizedPrefixIndices
      D N W m (lockingThreshold D N) leftPrefix.1 :=
    (Finset.mem_filter.mp leftIndex.2).1
  have hrightRealized : rightIndex.1 ∈ realizedPrefixIndices
      D N W m (lockingThreshold D N) rightPrefix.1 :=
    (Finset.mem_filter.mp rightIndex.2).1
  have hleftPrefix : lockingPrefix D.positiveEnumeration leftIndex.1 m
        (lockingThreshold D N) = leftPrefix.1 :=
    (Finset.mem_filter.mp hleftRealized).2
  have hrightPrefix : lockingPrefix D.positiveEnumeration rightIndex.1 m
        (lockingThreshold D N) = rightPrefix.1 :=
    (Finset.mem_filter.mp hrightRealized).2
  have hprefixValue : leftPrefix.1 = rightPrefix.1 := by
    rw [← hleftPrefix, ← hrightPrefix, hindexValue]
  have hprefix : leftPrefix = rightPrefix := Subtype.ext hprefixValue
  subst rightPrefix
  have hindex : leftIndex = rightIndex := Subtype.ext hindexValue
  subst rightIndex
  rfl

/-- Summing eligible indices over all canonical nonrare prefix fibres never
counts an original window index more than once. -/
theorem globalActualInteriorEligibleCount_le (D : CarrySeries)
    {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    (∑ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      (interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        threshold).card) ≤
      enumeratedWindowCount D.positiveEnumeration N W := by
  classical
  have hcard := Fintype.card_le_of_injective
    (globalActualInteriorEligibleIndexToWindow D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) (threshold := threshold))
    (globalActualInteriorEligibleIndexToWindow_injective D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) (threshold := threshold))
  calc
    (∑ pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N),
        (interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold).card) =
        Fintype.card (GlobalActualInteriorEligibleIndex D hgeom hW hscale
          hpositiveFrom threshold) := by
            simp only [Fintype.card_sigma, Fintype.card_coe]
    _ ≤ Fintype.card ↥(windowIndices D.positiveEnumeration N W) := hcard
    _ = (windowIndices D.positiveEnumeration N W).card := by
      simp only [Fintype.card_coe]
    _ = enumeratedWindowCount D.positiveEnumeration N W :=
      card_windowIndices D.positiveEnumeration N W

/-- Every globally eligible anchor has the same proved block-scale cap,
including anchors that contribute only to the terminal-loss term. -/
theorem globalActualInteriorEligibleBlockScale_le_cap (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N))
    (k : ↥(interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
      (globalActualInteriorThreshold D N W m cap reserve))) :
    actualInteriorBlockScale D pfx.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        (globalActualInteriorThreshold D N W m cap reserve) k ≤
      globalActualInteriorBlockScaleCap D N W cap := by
  apply actualInteriorBlockScale_le_of_state_den_le D hgeom pfx.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
  · exact globalActualInteriorThreshold_covers
      D hgeom hW hscale hpositiveFrom hw reserve pfx
  · exact canonicalLockedTopState_den_le_cap
      D hgeom hW hscale hpositiveFrom hw pfx

/-- The canonical threshold contains the full retained-cover margin for
every eligible anchor, independently of whether that anchor has a retained
block. -/
theorem globalActualInteriorThreshold_covers_eligible (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N))
    (k : ↥(interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
      (globalActualInteriorThreshold D N W m cap reserve))) :
    Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den +
        2 * cap +
          24 * actualInteriorBlockScale D pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            (globalActualInteriorThreshold D N W m cap reserve) k ≤
      globalActualInteriorThreshold D N W m cap reserve := by
  have hlog : Nat.log 2 (PolynomialGraph.normalizedTopState
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        D.denominator D.weight).den ≤
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) :=
    Nat.log_mono_right (canonicalLockedTopState_den_le_cap
      D hgeom hW hscale hpositiveFrom hw pfx)
  have hell := globalActualInteriorEligibleBlockScale_le_cap
    D hw pfx k
  conv_rhs => rw [globalActualInteriorThreshold]
  omega

/-- Total genuine stabilized interior span over every globally eligible
nonrare window index. -/
noncomputable def globalActualInteriorEligibleStabilizedMass (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) : ℕ :=
  ∑ pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N),
    ∑ k : ↥(interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx) threshold),
      Erdos260.GapWord.span (actualStabilizedInteriorWord D pfx.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        threshold k)

/-- Global actual interior cover.  The retained deep mass is charged through
the proved source map, while every shallow terminal loss is charged once to
its original window index. -/
theorem globalActualInteriorEligibleStabilizedMass_le_deep_add_terminal
    (D : CarrySeries) {N W m cap reserve F : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve) ≤
      4 * (∑ source ∈ globalActualInteriorDeepSources D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom)
          (globalActualInteriorThreshold D N W m cap reserve) F,
        globalActualInteriorBlockSpan D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) source) +
        4 * enumeratedWindowCount D.positiveEnumeration N W *
          (F + 4 * globalActualInteriorBlockScaleCap D N W cap) := by
  classical
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let terminalCap := F + 4 * globalActualInteriorBlockScaleCap D N W cap
  have hlocal (pfx : CanonicalNonrarePrefix
      D N W m (lockingThreshold D N)) :
      (∑ k : ↥(interiorEligibleIndices D N W m (lockingThreshold D N)
          pfx.1 (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold),
        Erdos260.GapWord.span (actualStabilizedInteriorWord D pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold k)) ≤
        4 * actualInteriorDeepRetainedMass D
          (N := N) (W := W) (m := m)
          (bound := lockingThreshold D N) pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold F +
        4 * Finset.univ.sum (fun k : ↥(interiorEligibleIndices
            D N W m (lockingThreshold D N) pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold) =>
          F + 4 * actualInteriorBlockScale D pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold k) := by
    apply actualInteriorEligible_stabilizedSpan_le_deepMass_add_terminal
      D hw hgeom pfx.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        threshold F
    · simpa only [threshold] using globalActualInteriorThreshold_covers
        D hgeom hW hscale hpositiveFrom hw reserve pfx
    · intro k
      simpa only [threshold] using
        globalActualInteriorThreshold_covers_eligible D hw pfx k
  have hterminalPrefix (pfx : CanonicalNonrarePrefix
      D N W m (lockingThreshold D N)) :
      Finset.univ.sum (fun k : ↥(interiorEligibleIndices
          D N W m (lockingThreshold D N)
          pfx.1 (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold) =>
        F + 4 * actualInteriorBlockScale D pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold k) ≤
        (interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold).card * terminalCap := by
    calc
      Finset.univ.sum (fun k : ↥(interiorEligibleIndices
            D N W m (lockingThreshold D N)
            pfx.1 (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold) =>
          F + 4 * actualInteriorBlockScale D pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold k) ≤
          Finset.univ.sum (fun _k : ↥(interiorEligibleIndices D N W m
            (lockingThreshold D N) pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold) => terminalCap) := by
        apply Finset.sum_le_sum
        intro k _hk
        dsimp only [terminalCap]
        gcongr
        simpa only [threshold] using
          globalActualInteriorEligibleBlockScale_le_cap D hw pfx k
      _ = (interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold).card * terminalCap := by
        simp
  have hterminal :
      Finset.univ.sum (fun pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N) =>
        Finset.univ.sum (fun k : ↥(interiorEligibleIndices
          D N W m (lockingThreshold D N)
          pfx.1 (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold) =>
          F + 4 * actualInteriorBlockScale D pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold k)) ≤
        enumeratedWindowCount D.positiveEnumeration N W * terminalCap := by
    calc
      Finset.univ.sum (fun pfx : CanonicalNonrarePrefix
            D N W m (lockingThreshold D N) =>
          Finset.univ.sum (fun k : ↥(interiorEligibleIndices
            D N W m (lockingThreshold D N)
            pfx.1 (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold) =>
            F + 4 * actualInteriorBlockScale D pfx.1
              (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
              threshold k)) ≤
          Finset.univ.sum (fun pfx : CanonicalNonrarePrefix
              D N W m (lockingThreshold D N) =>
            (interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
              (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
              threshold).card * terminalCap) := by
        apply Finset.sum_le_sum
        intro pfx _hpfx
        exact hterminalPrefix pfx
      _ = (Finset.univ.sum (fun pfx : CanonicalNonrarePrefix
              D N W m (lockingThreshold D N) =>
            (interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
              (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
              threshold).card)) * terminalCap := by
        rw [Finset.sum_mul]
      _ ≤ enumeratedWindowCount D.positiveEnumeration N W * terminalCap :=
        Nat.mul_le_mul_right terminalCap (by
          simpa only [threshold] using globalActualInteriorEligibleCount_le
            D hgeom hW hscale hpositiveFrom
            (threshold := globalActualInteriorThreshold D N W m cap reserve))
  have hsumLocal :
      globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
          hpositiveFrom threshold ≤
        ∑ pfx : CanonicalNonrarePrefix
            D N W m (lockingThreshold D N),
          (4 * actualInteriorDeepRetainedMass D
            (N := N) (W := W) (m := m)
            (bound := lockingThreshold D N) pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold F +
          4 * Finset.univ.sum (fun k : ↥(interiorEligibleIndices
              D N W m (lockingThreshold D N) pfx.1
              (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
              threshold) =>
            F + 4 * actualInteriorBlockScale D pfx.1
              (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
              threshold k)) := by
    unfold globalActualInteriorEligibleStabilizedMass
    apply Finset.sum_le_sum
    intro pfx _hpfx
    exact hlocal pfx
  calc
    globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve) =
        globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
          hpositiveFrom threshold := rfl
    _ ≤ ∑ pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N),
        (4 * actualInteriorDeepRetainedMass D
          (N := N) (W := W) (m := m)
          (bound := lockingThreshold D N) pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold F +
        4 * Finset.univ.sum (fun k : ↥(interiorEligibleIndices
            D N W m (lockingThreshold D N) pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold) =>
          F + 4 * actualInteriorBlockScale D pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold k)) := hsumLocal
    _ = 4 * (∑ pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N),
        actualInteriorDeepRetainedMass D
          (N := N) (W := W) (m := m)
          (bound := lockingThreshold D N) pfx.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          threshold F) +
        4 * (∑ pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N),
        Finset.univ.sum (fun k : ↥(interiorEligibleIndices
            D N W m (lockingThreshold D N) pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold) =>
          F + 4 * actualInteriorBlockScale D pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold k)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 4 * (∑ source ∈ globalActualInteriorDeepSources D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) threshold F,
        globalActualInteriorBlockSpan D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) source) +
        4 * (∑ pfx : CanonicalNonrarePrefix
          D N W m (lockingThreshold D N),
        Finset.univ.sum (fun k : ↥(interiorEligibleIndices
            D N W m (lockingThreshold D N) pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold) =>
          F + 4 * actualInteriorBlockScale D pfx.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
            threshold k)) := by
      rw [globalActualInteriorDeepBlockSpan_sum
        D hgeom hW hscale hpositiveFrom]
    _ ≤ 4 * (∑ source ∈ globalActualInteriorDeepSources D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) threshold F,
        globalActualInteriorBlockSpan D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) source) +
        4 * enumeratedWindowCount D.positiveEnumeration N W * terminalCap := by
      apply Nat.add_le_add_left
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hterminal
    _ = 4 * (∑ source ∈ globalActualInteriorDeepSources D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom)
          (globalActualInteriorThreshold D N W m cap reserve) F,
        globalActualInteriorBlockSpan D
          (hgeom := hgeom) (hW := hW) (hscale := hscale)
          (hpositiveFrom := hpositiveFrom) source) +
        4 * enumeratedWindowCount D.positiveEnumeration N W *
          (F + 4 * globalActualInteriorBlockScaleCap D N W cap) := rfl

/-! ## Finite four-class window assembly -/

/-- Explicit span cutoff that pays for the locking prefix, all boundary
states, and two copies of the canonical continuation threshold. -/
def globalActualClassificationCutoff (D : CarrySeries)
    (N W m cap reserve : ℕ) : ℕ :=
  lockingThreshold D N + 2 * cap + m +
    2 * globalActualInteriorThreshold D N W m cap reserve

/-- Windows below the complete finite classification cutoff. -/
def globalActualShortWindowIndices (D : CarrySeries)
    (N W m cap reserve : ℕ) : Finset ℕ :=
  (windowIndices D.positiveEnumeration N W).filter fun k =>
    forwardSpan D.positiveEnumeration k m ≤
      globalActualClassificationCutoff D N W m cap reserve

/-- Realized locking prefixes whose fibres have at most `d+1` members. -/
def globalActualRarePrefixes (D : CarrySeries)
    (N W m : ℕ) : Finset Erdos260.GapWord :=
  (realizedLockingPrefixes D.positiveEnumeration N W m
      (lockingThreshold D N)).filter fun pfx =>
    (realizedPrefixIndices D N W m (lockingThreshold D N) pfx).card ≤
      D.weight.natDegree + 1

/-- All long-window indices belonging to an actual rare locking prefix. -/
def globalActualRareWindowIndices (D : CarrySeries)
    (N W m : ℕ) : Finset ℕ :=
  rarePrefixWindows
    (longWindowIndices D.positiveEnumeration N W m (lockingThreshold D N))
    (fun k => lockingPrefix D.positiveEnumeration k m
      (lockingThreshold D N))
    (globalActualRarePrefixes D N W m)

/-- Union of the genuine exterior-eligible fibres of all canonical nonrare
prefixes. -/
noncomputable def globalActualExteriorEligibleWindowIndices (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) : Finset ℕ := by
  classical
  exact (canonicalNonrarePrefixes D N W m
      (lockingThreshold D N)).attach.biUnion fun pfx =>
    exteriorEligibleIndices D N W m (lockingThreshold D N) pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx) threshold

/-- Union of the genuine interior-eligible fibres of all canonical nonrare
prefixes. -/
noncomputable def globalActualInteriorEligibleWindowIndices (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) : Finset ℕ := by
  classical
  exact (canonicalNonrarePrefixes D N W m
      (lockingThreshold D N)).attach.biUnion fun pfx =>
    interiorEligibleIndices D N W m (lockingThreshold D N) pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx) threshold

/-- Interior windows not already charged to the exterior branch. -/
noncomputable def globalActualInteriorOnlyWindowIndices (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) : Finset ℕ :=
  globalActualInteriorEligibleWindowIndices D hgeom hW hscale
      hpositiveFrom threshold \
    globalActualExteriorEligibleWindowIndices D hgeom hW hscale
      hpositiveFrom threshold

/-- Every original window lies in one of the four actual finite classes.
For a nonshort nonrare window, failure of exterior eligibility forces enough
interior span by the exact interior/boundary/exterior span partition. -/
theorem globalActualWindowIndices_subset_fourClasses (D : CarrySeries)
    {N W m cap reserve : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    windowIndices D.positiveEnumeration N W ⊆
      globalActualShortWindowIndices D N W m cap reserve ∪
        (globalActualRareWindowIndices D N W m ∪
          (globalActualExteriorEligibleWindowIndices D hgeom hW hscale
              hpositiveFrom
              (globalActualInteriorThreshold D N W m cap reserve) ∪
            globalActualInteriorOnlyWindowIndices D hgeom hW hscale
              hpositiveFrom
              (globalActualInteriorThreshold D N W m cap reserve))) := by
  classical
  intro k hkWindow
  let bound := lockingThreshold D N
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let cutoff := globalActualClassificationCutoff D N W m cap reserve
  by_cases hshort : forwardSpan D.positiveEnumeration k m ≤ cutoff
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_filter.mpr ⟨hkWindow, by simpa only [cutoff] using hshort⟩
  · have hcutoff : cutoff < forwardSpan D.positiveEnumeration k m :=
      Nat.lt_of_not_ge hshort
    have hlong : k ∈ longWindowIndices D.positiveEnumeration N W m bound := by
      rw [mem_longWindowIndices_iff]
      refine ⟨hkWindow, ?_⟩
      dsimp only [cutoff, globalActualClassificationCutoff, bound] at hcutoff ⊢
      omega
    let pfx := lockingPrefix D.positiveEnumeration k m bound
    have hpfxRealized : pfx ∈ realizedLockingPrefixes
        D.positiveEnumeration N W m bound := by
      rw [realizedLockingPrefixes, Finset.mem_image]
      exact ⟨k, hlong, rfl⟩
    by_cases hrare :
        (realizedPrefixIndices D N W m bound pfx).card ≤
          D.weight.natDegree + 1
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      unfold globalActualRareWindowIndices rarePrefixWindows
      apply Finset.mem_filter.mpr
      refine ⟨hlong, ?_⟩
      unfold globalActualRarePrefixes
      exact Finset.mem_filter.mpr ⟨hpfxRealized, hrare⟩
    · have hnonrareCard : D.weight.natDegree + 1 <
          (realizedPrefixIndices D N W m bound pfx).card :=
        Nat.lt_of_not_ge hrare
      have hpfxNonrare : pfx ∈ canonicalNonrarePrefixes
          D N W m bound := by
        rw [mem_canonicalNonrarePrefixes_iff]
        exact ⟨hpfxRealized, hnonrareCard⟩
      let pfxSource : CanonicalNonrarePrefix D N W m bound :=
        ⟨pfx, hpfxNonrare⟩
      let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfxSource
      have hkRealized : k ∈ realizedPrefixIndices D N W m bound pfx := by
        apply Finset.mem_filter.mpr
        exact ⟨hlong, rfl⟩
      let post := postLockingWord D.positiveEnumeration k m bound
      let μ : ℝ :=
        (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
      by_cases hext : threshold < exteriorSpanAlong D.base post μ
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        left
        unfold globalActualExteriorEligibleWindowIndices
        rw [Finset.mem_biUnion]
        refine ⟨pfxSource, by simp, ?_⟩
        apply Finset.mem_filter.mpr
        simpa only [pfxSource, G, pfx, post, μ, threshold] using
          And.intro hkRealized hext
      · have hextLe : exteriorSpanAlong D.base post μ ≤ threshold :=
          Nat.le_of_not_gt hext
        have hpfxBounds := realizedLockingPrefix_bounds
          D.positiveEnumeration hgeom hpfxRealized
        have hpfxSpan : Erdos260.GapWord.span pfx ≤ bound + cap :=
          hpfxBounds.2.2.1
        have hpostPositive : Erdos260.GapWord.Positive post := by
          simpa only [post] using
            postLockingWord_positive D.positiveEnumeration k m bound
        have hpostCap : ∀ g ∈ post, g ≤ cap := by
          simpa only [post] using postLockingWord_gap_le D hgeom hlong
        have hboundary : boundarySpanAlong D.base post μ ≤
            cap + post.length :=
          boundarySpanAlong_le_cap_add_length D.base_ge_two
            hpostPositive hpostCap μ
        have hpostLength : post.length ≤ m := by
          simpa only [post] using
            postLockingWord_length_le D.positiveEnumeration k m bound
        have hclassified := classifiedSpanAlong D.base D.base_ge_two post μ
        have hsplit := lockingPrefix_span_add_postSpan
          D.positiveEnumeration k m bound
        have hinterior : threshold < interiorSpanAlong D.base post μ := by
          dsimp only [cutoff, globalActualClassificationCutoff,
            threshold, bound] at hcutoff
          dsimp only [pfx, bound] at hpfxSpan
          dsimp only [post, bound] at hextLe hboundary hpostLength hclassified hsplit
          dsimp only [post, bound]
          omega
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        right
        unfold globalActualInteriorOnlyWindowIndices
        apply Finset.mem_sdiff.mpr
        constructor
        · unfold globalActualInteriorEligibleWindowIndices
          rw [Finset.mem_biUnion]
          refine ⟨pfxSource, by simp, ?_⟩
          apply Finset.mem_filter.mpr
          simpa only [pfxSource, G, pfx, post, μ, threshold] using
            And.intro hkRealized hinterior
        · intro hkExterior
          unfold globalActualExteriorEligibleWindowIndices at hkExterior
          rw [Finset.mem_biUnion] at hkExterior
          rcases hkExterior with ⟨otherPrefix, _hattach, hkOther⟩
          have hkOtherRealized : k ∈ realizedPrefixIndices D N W m
              (lockingThreshold D N) otherPrefix.1 :=
            (Finset.mem_filter.mp hkOther).1
          have hotherValue : otherPrefix.1 = pfx := by
            have hprefix := (Finset.mem_filter.mp hkOtherRealized).2
            simpa only [pfx, bound] using hprefix.symm
          have hother : otherPrefix = pfxSource := Subtype.ext hotherValue
          subst otherPrefix
          apply hext
          have hkOtherExterior := (Finset.mem_filter.mp hkOther).2
          simpa only [pfxSource, G, pfx, post, μ, threshold, bound] using
            hkOtherExterior

theorem globalActualShortWindowIndices_subset_windowIndices (D : CarrySeries)
    (N W m cap reserve : ℕ) :
    globalActualShortWindowIndices D N W m cap reserve ⊆
      windowIndices D.positiveEnumeration N W := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

theorem globalActualRareWindowIndices_subset_windowIndices (D : CarrySeries)
    (N W m : ℕ) :
    globalActualRareWindowIndices D N W m ⊆
      windowIndices D.positiveEnumeration N W := by
  intro k hk
  have hlong := (Finset.mem_filter.mp hk).1
  exact (Finset.mem_filter.mp hlong).1

theorem globalActualExteriorEligibleWindowIndices_subset_windowIndices
    (D : CarrySeries) {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    globalActualExteriorEligibleWindowIndices D hgeom hW hscale
        hpositiveFrom threshold ⊆
      windowIndices D.positiveEnumeration N W := by
  classical
  intro k hk
  unfold globalActualExteriorEligibleWindowIndices at hk
  rw [Finset.mem_biUnion] at hk
  rcases hk with ⟨pfx, _hpfx, hk⟩
  have hrealized := (Finset.mem_filter.mp hk).1
  have hlong := (Finset.mem_filter.mp hrealized).1
  exact (Finset.mem_filter.mp hlong).1

theorem globalActualInteriorEligibleWindowIndices_subset_windowIndices
    (D : CarrySeries) {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    globalActualInteriorEligibleWindowIndices D hgeom hW hscale
        hpositiveFrom threshold ⊆
      windowIndices D.positiveEnumeration N W := by
  classical
  intro k hk
  unfold globalActualInteriorEligibleWindowIndices at hk
  rw [Finset.mem_biUnion] at hk
  rcases hk with ⟨pfx, _hpfx, hk⟩
  have hrealized := (Finset.mem_filter.mp hk).1
  have hlong := (Finset.mem_filter.mp hrealized).1
  exact (Finset.mem_filter.mp hlong).1

theorem globalActualInteriorOnlyWindowIndices_subset_windowIndices
    (D : CarrySeries) {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    globalActualInteriorOnlyWindowIndices D hgeom hW hscale
        hpositiveFrom threshold ⊆
      windowIndices D.positiveEnumeration N W := by
  intro k hk
  exact globalActualInteriorEligibleWindowIndices_subset_windowIndices
    D hgeom hW hscale hpositiveFrom (Finset.mem_sdiff.mp hk).1

/-- Exact finite four-class mass inequality.  No asymptotic notation or
unproved partition assumption occurs in this assembly. -/
theorem globalActualForwardSpanMass_le_fourClassMasses (D : CarrySeries)
    {N W m cap reserve : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    forwardSpanMass D.positiveEnumeration N W m ≤
      (∑ k ∈ globalActualShortWindowIndices D N W m cap reserve,
          forwardSpan D.positiveEnumeration k m) +
        ((∑ k ∈ globalActualRareWindowIndices D N W m,
            forwardSpan D.positiveEnumeration k m) +
          ((∑ k ∈ globalActualExteriorEligibleWindowIndices
              D hgeom hW hscale hpositiveFrom
                (globalActualInteriorThreshold D N W m cap reserve),
              forwardSpan D.positiveEnumeration k m) +
            ∑ k ∈ globalActualInteriorOnlyWindowIndices
              D hgeom hW hscale hpositiveFrom
                (globalActualInteriorThreshold D N W m cap reserve),
              forwardSpan D.positiveEnumeration k m)) := by
  classical
  let windows := windowIndices D.positiveEnumeration N W
  let short := globalActualShortWindowIndices D N W m cap reserve
  let rare := globalActualRareWindowIndices D N W m
  let exterior := globalActualExteriorEligibleWindowIndices
    D hgeom hW hscale hpositiveFrom
      (globalActualInteriorThreshold D N W m cap reserve)
  let interior := globalActualInteriorOnlyWindowIndices
    D hgeom hW hscale hpositiveFrom
      (globalActualInteriorThreshold D N W m cap reserve)
  let span : ℕ → ℕ := fun k => forwardSpan D.positiveEnumeration k m
  have hcover : windows ⊆ short ∪ (rare ∪ (exterior ∪ interior)) := by
    simpa only [windows, short, rare, exterior, interior] using
      globalActualWindowIndices_subset_fourClasses
        D hgeom hW hscale hpositiveFrom
  have hshortSubset : short ⊆ windows := by
    simpa only [short, windows] using
      globalActualShortWindowIndices_subset_windowIndices
        D N W m cap reserve
  have hrareSubset : rare ⊆ windows := by
    simpa only [rare, windows] using
      globalActualRareWindowIndices_subset_windowIndices D N W m
  have hexteriorSubset : exterior ⊆ windows := by
    simpa only [exterior, windows] using
      globalActualExteriorEligibleWindowIndices_subset_windowIndices
        D hgeom hW hscale hpositiveFrom
  have hinteriorSubset : interior ⊆ windows := by
    simpa only [interior, windows] using
      globalActualInteriorOnlyWindowIndices_subset_windowIndices
        D hgeom hW hscale hpositiveFrom
  have indicatorSum (s : Finset ℕ) (hs : s ⊆ windows) :
      (∑ k ∈ windows, if k ∈ s then span k else 0) =
        ∑ k ∈ s, span k := by
    have hfilter : windows.filter (fun k => k ∈ s) = s := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · exact fun hk => hk.2
      · exact fun hk => ⟨hs hk, hk⟩
    rw [← Finset.sum_filter, hfilter]
  unfold forwardSpanMass
  change (∑ k ∈ windows, span k) ≤ _
  calc
    (∑ k ∈ windows, span k) ≤
        Finset.sum windows (fun k =>
          (if k ∈ short then span k else 0) +
            ((if k ∈ rare then span k else 0) +
              ((if k ∈ exterior then span k else 0) +
                (if k ∈ interior then span k else 0)))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkClass := hcover hk
      simp only [Finset.mem_union] at hkClass
      rcases hkClass with hkShort | hkRare | hkExterior | hkInterior
      · simp only [hkShort, if_true]
        omega
      · simp only [hkRare, if_true]
        omega
      · simp only [hkExterior, if_true]
        omega
      · simp only [hkInterior, if_true]
        omega
    _ = (∑ k ∈ short, span k) +
        ((∑ k ∈ rare, span k) +
          ((∑ k ∈ exterior, span k) +
            ∑ k ∈ interior, span k)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      rw [indicatorSum short hshortSubset, indicatorSum rare hrareSubset,
        indicatorSum exterior hexteriorSubset,
        indicatorSum interior hinteriorSubset]
    _ = _ := rfl

/-- Explicit short-window mass bound at the complete classification cutoff. -/
theorem globalActualShortWindowMass_le (D : CarrySeries)
    (N W m cap reserve : ℕ) :
    (∑ k ∈ globalActualShortWindowIndices D N W m cap reserve,
        forwardSpan D.positiveEnumeration k m) ≤
      globalActualClassificationCutoff D N W m cap reserve *
        enumeratedWindowCount D.positiveEnumeration N W := by
  let short := globalActualShortWindowIndices D N W m cap reserve
  let cutoff := globalActualClassificationCutoff D N W m cap reserve
  calc
    (∑ k ∈ short, forwardSpan D.positiveEnumeration k m) ≤
        ∑ _k ∈ short, cutoff := by
      apply Finset.sum_le_sum
      intro k hk
      exact (Finset.mem_filter.mp hk).2
    _ = short.card * cutoff := by simp
    _ ≤ (windowIndices D.positiveEnumeration N W).card * cutoff := by
      exact Nat.mul_le_mul_right cutoff (Finset.card_le_card
        (globalActualShortWindowIndices_subset_windowIndices
          D N W m cap reserve))
    _ = cutoff * enumeratedWindowCount D.positiveEnumeration N W := by
      rw [card_windowIndices]
      exact Nat.mul_comm _ _

/-- Exact rare-prefix mass bound on the genuine realized prefix fibres. -/
theorem globalActualRareWindowMass_le (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap) :
    (∑ k ∈ globalActualRareWindowIndices D N W m,
        forwardSpan D.positiveEnumeration k m) ≤
      (globalActualRarePrefixes D N W m).card *
        (D.weight.natDegree + 1) * (m * cap) := by
  unfold globalActualRareWindowIndices
  apply eq_rare
  · intro p hp
    have hpRare := (Finset.mem_filter.mp hp).2
    simpa only [realizedPrefixIndices] using hpRare
  · intro k hk
    have hlong := (Finset.mem_filter.mp hk).1
    have hwindow := (Finset.mem_filter.mp hlong).1
    exact WindowGeometry.forwardSpan_le D.positiveEnumeration hgeom hwindow

theorem globalActualRarePrefixes_card_le_compositions (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap) :
    (globalActualRarePrefixes D N W m).card ≤
      ∑ r ∈ Finset.Icc 0 m,
        (lockingThreshold D N + cap).choose r := by
  calc
    (globalActualRarePrefixes D N W m).card ≤
        (realizedLockingPrefixes D.positiveEnumeration N W m
          (lockingThreshold D N)).card := by
      apply Finset.card_le_card
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    _ ≤ ∑ r ∈ Finset.Icc 0 m,
        (lockingThreshold D N + cap).choose r :=
      realizedLockingPrefixes_card_le_compositions
        D.positiveEnumeration hgeom

/-- Total actual exterior window mass, still indexed by its canonical
nonrare prefix fibre. -/
noncomputable def globalActualExteriorEligibleMass (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) : ℕ :=
  ∑ pfx ∈ (canonicalNonrarePrefixes D N W m
      (lockingThreshold D N)).attach,
    ∑ k ∈ exteriorEligibleIndices D N W m (lockingThreshold D N) pfx.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx) threshold,
      forwardSpan D.positiveEnumeration k m

/-- Exterior fibres belonging to distinct canonical locking prefixes are
disjoint because an enumeration index determines its locking prefix. -/
theorem globalActualExteriorEligibleFibres_pairwiseDisjoint (D : CarrySeries)
    {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    Set.PairwiseDisjoint
      (↑((canonicalNonrarePrefixes D N W m
        (lockingThreshold D N)).attach))
      (fun pfx => exteriorEligibleIndices D N W m (lockingThreshold D N)
        pfx.1 (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
        threshold) := by
  classical
  intro left _hleft right _hright hne
  change Disjoint
    (exteriorEligibleIndices D N W m (lockingThreshold D N) left.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom left) threshold)
    (exteriorEligibleIndices D N W m (lockingThreshold D N) right.1
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom right) threshold)
  rw [Finset.disjoint_left]
  intro k hkLeft hkRight
  have hleftRealized := (Finset.mem_filter.mp hkLeft).1
  have hrightRealized := (Finset.mem_filter.mp hkRight).1
  have hleftPrefix := (Finset.mem_filter.mp hleftRealized).2
  have hrightPrefix := (Finset.mem_filter.mp hrightRealized).2
  apply hne
  apply Subtype.ext
  exact hleftPrefix.symm.trans hrightPrefix

/-- The union form used in the four-class partition has exactly the same
mass as the dependent prefix-indexed exterior source family. -/
theorem globalActualExteriorEligibleWindowMass_eq (D : CarrySeries)
    {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    (∑ k ∈ globalActualExteriorEligibleWindowIndices
        D hgeom hW hscale hpositiveFrom threshold,
      forwardSpan D.positiveEnumeration k m) =
      globalActualExteriorEligibleMass D hgeom hW hscale
        hpositiveFrom threshold := by
  classical
  unfold globalActualExteriorEligibleWindowIndices
    globalActualExteriorEligibleMass
  rw [Finset.sum_biUnion
    (globalActualExteriorEligibleFibres_pairwiseDisjoint
      D hgeom hW hscale hpositiveFrom)]

/-- Sum of the exact per-prefix exterior census bounds. -/
noncomputable def globalActualExteriorCensusBound (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) : ℝ :=
  ∑ pfx ∈ (canonicalNonrarePrefixes D N W m
      (lockingThreshold D N)).attach,
    let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx
    (Fintype.card (PreExteriorRecord D.base cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
    (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) *
    (D.weight.natDegree + 2 * D.weight.natDegree *
      (((D.heightNatConstant * (N + W + m * cap + 1) ^
            D.weight.natDegree : ℕ) : ℝ) *
          ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
          (D.base - 1 : ℝ) /
        (D.base : ℝ) ^ threshold) ^
          (((D.weight.natDegree : ℝ))⁻¹)) *
    (m * cap : ℕ)

/-- Global finite exterior proposition obtained by summing the proved actual
per-prefix source census. -/
theorem globalActualExteriorEligibleMass_cast_le_census (D : CarrySeries)
    {N W m cap threshold : ℕ}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    (globalActualExteriorEligibleMass D hgeom hW hscale
        hpositiveFrom threshold : ℝ) ≤
      globalActualExteriorCensusBound D hgeom hW hscale
        hpositiveFrom threshold := by
  classical
  unfold globalActualExteriorEligibleMass globalActualExteriorCensusBound
  push_cast
  apply Finset.sum_le_sum
  intro pfx _hpfx
  have h := prop_exterior D hd hw hgeom hpositiveFrom pfx.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
    (canonicalLockedGraph_fit D hgeom hW hscale hpositiveFrom pfx)
    threshold
  push_cast at h
  simpa only using h

/-- Per-window deterministic loss when converting a complete interior-only
window span to the stabilized interior word used by the census. -/
def globalActualInteriorAssemblyLoss (D : CarrySeries)
    (N W m cap reserve : ℕ) : ℕ :=
  lockingThreshold D N + 4 * cap + m +
    globalActualInteriorThreshold D N W m cap reserve +
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap)

/-- Eligible dependent sources whose original window belongs to the
interior-only class of the four-way partition. -/
noncomputable def globalActualInteriorOnlyEligibleSources (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (reserve : ℕ) :
    Finset (GlobalActualInteriorEligibleIndex D hgeom hW hscale
      hpositiveFrom
      (globalActualInteriorThreshold D N W m cap reserve)) := by
  classical
  exact Finset.univ.filter fun source =>
    source.2.1 ∈ globalActualInteriorOnlyWindowIndices
      D hgeom hW hscale hpositiveFrom
        (globalActualInteriorThreshold D N W m cap reserve)

/-- The underlying enumeration index is injective on the complete dependent
eligible source type. -/
theorem globalActualInteriorEligibleSourceIndex_injective (D : CarrySeries)
    {N W m cap threshold : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} :
    Function.Injective fun source : GlobalActualInteriorEligibleIndex
        D hgeom hW hscale hpositiveFrom threshold => source.2.1 := by
  intro left right hindex
  apply globalActualInteriorEligibleIndexToWindow_injective D
  apply Subtype.ext
  exact hindex

/-- The image of interior-only dependent sources is exactly the
interior-only window Finset. -/
theorem globalActualInteriorOnlyEligibleSources_image (D : CarrySeries)
    {N W m cap reserve : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    (globalActualInteriorOnlyEligibleSources D hgeom hW hscale
      hpositiveFrom reserve).image (fun source => source.2.1) =
        globalActualInteriorOnlyWindowIndices D hgeom hW hscale
          hpositiveFrom
            (globalActualInteriorThreshold D N W m cap reserve) := by
  classical
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨source, hsource, rfl⟩
    exact (Finset.mem_filter.mp hsource).2
  · intro hk
    have hkInterior := (Finset.mem_sdiff.mp hk).1
    unfold globalActualInteriorEligibleWindowIndices at hkInterior
    rw [Finset.mem_biUnion] at hkInterior
    rcases hkInterior with ⟨pfx, _hpfx, hkEligible⟩
    let source : GlobalActualInteriorEligibleIndex D hgeom hW hscale
        hpositiveFrom
        (globalActualInteriorThreshold D N W m cap reserve) :=
      ⟨pfx, ⟨k, hkEligible⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨source, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ source, hk⟩

/-- A source retained in the interior-only class has exterior span at most
the common continuation threshold. -/
theorem globalActualInteriorOnlySource_exteriorSpan_le (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (source : GlobalActualInteriorEligibleIndex D hgeom hW hscale
      hpositiveFrom
      (globalActualInteriorThreshold D N W m cap reserve))
    (hsource : source ∈ globalActualInteriorOnlyEligibleSources
      D hgeom hW hscale hpositiveFrom reserve) :
    exteriorSpanAlong D.base
        (postLockingWord D.positiveEnumeration source.2.1 m
          (lockingThreshold D N))
        (((PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
          D.denominator D.weight : ℚ) : ℝ)) ≤
      globalActualInteriorThreshold D N W m cap reserve := by
  apply Nat.le_of_not_gt
  intro hext
  have hkExterior : source.2.1 ∈
      globalActualExteriorEligibleWindowIndices D hgeom hW hscale
        hpositiveFrom
          (globalActualInteriorThreshold D N W m cap reserve) := by
    unfold globalActualExteriorEligibleWindowIndices
    rw [Finset.mem_biUnion]
    refine ⟨source.1, by simp, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp source.2.2).1, hext⟩
  have hkOnly := (Finset.mem_filter.mp hsource).2
  exact (Finset.mem_sdiff.mp hkOnly).2 hkExterior

/-- Pointwise conversion from a complete interior-only forward span to its
stabilized interior word plus the explicit deterministic loss. -/
theorem globalActualInteriorOnlySource_forwardSpan_le (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (source : GlobalActualInteriorEligibleIndex D hgeom hW hscale
      hpositiveFrom
      (globalActualInteriorThreshold D N W m cap reserve))
    (hsource : source ∈ globalActualInteriorOnlyEligibleSources
      D hgeom hW hscale hpositiveFrom reserve) :
    forwardSpan D.positiveEnumeration source.2.1 m ≤
      Erdos260.GapWord.span
        (actualStabilizedInteriorWord D source.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
          (globalActualInteriorThreshold D N W m cap reserve) source.2) +
      globalActualInteriorAssemblyLoss D N W m cap reserve := by
  let bound := lockingThreshold D N
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1
  let post := postLockingWord D.positiveEnumeration source.2.1 m bound
  let μ : ℝ := (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  have hkRealized : source.2.1 ∈ realizedPrefixIndices D N W m
      bound source.1.1 := (Finset.mem_filter.mp source.2.2).1
  have hpfxEq : lockingPrefix D.positiveEnumeration source.2.1 m bound =
      source.1.1 := (Finset.mem_filter.mp hkRealized).2
  have hprefixRealized : source.1.1 ∈ realizedLockingPrefixes
      D.positiveEnumeration N W m bound :=
    (mem_canonicalNonrarePrefixes_iff D).mp source.1.2 |>.1
  have hpfxSpan : Erdos260.GapWord.span source.1.1 ≤ bound + cap :=
    (realizedLockingPrefix_bounds D.positiveEnumeration hgeom
      hprefixRealized).2.2.1
  have hpostPositive : Erdos260.GapWord.Positive post := by
    simpa only [post] using
      postLockingWord_positive D.positiveEnumeration source.2.1 m bound
  have hpostCap : ∀ g ∈ post, g ≤ cap := by
    simpa only [post] using postLockingWord_gap_le D hgeom
      (Finset.mem_filter.mp hkRealized).1
  have hboundary : boundarySpanAlong D.base post μ ≤ cap + post.length :=
    boundarySpanAlong_le_cap_add_length D.base_ge_two
      hpostPositive hpostCap μ
  have hpostLength : post.length ≤ m := by
    simpa only [post] using
      postLockingWord_length_le D.positiveEnumeration source.2.1 m bound
  have hclassified := classifiedSpanAlong D.base D.base_ge_two post μ
  have hext := globalActualInteriorOnlySource_exteriorSpan_le
    D source hsource
  have hinterior := actualInteriorSpan_le_stabilizedSpan_add
    D hgeom source.1.1 G threshold source.2
  have hsplit := lockingPrefix_span_add_postSpan
    D.positiveEnumeration source.2.1 m bound
  rw [hpfxEq] at hsplit
  have hlog : Nat.log 2
      (G.normalizedTopState D.denominator D.weight).den ≤
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) :=
    Nat.log_mono_right (canonicalLockedTopState_den_le_cap
      D hgeom hW hscale hpositiveFrom hw source.1)
  dsimp only [globalActualInteriorAssemblyLoss]
  dsimp only [bound, threshold, G, post, μ] at hpfxSpan hboundary hpostLength
  dsimp only [bound, threshold, G, post, μ] at hclassified hext hinterior hsplit hlog
  omega

/-- Reindexing the dependent eligible source family gives exactly the global
stabilized mass definition. -/
theorem globalActualInteriorEligibleStabilizedMass_eq_sourceSum
    (D : CarrySeries) {N W m cap threshold : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom threshold =
      ∑ source : GlobalActualInteriorEligibleIndex D hgeom hW hscale
          hpositiveFrom threshold,
        Erdos260.GapWord.span
          (actualStabilizedInteriorWord D source.1.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
            threshold source.2) := by
  unfold globalActualInteriorEligibleStabilizedMass
  rw [Fintype.sum_sigma]

/-- Global interior-only forward mass is controlled by the stabilized census
mass plus one deterministic loss per original window. -/
theorem globalActualInteriorOnlyWindowMass_le_stabilized_add_loss
    (D : CarrySeries) {N W m cap reserve : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    (∑ k ∈ globalActualInteriorOnlyWindowIndices D hgeom hW hscale
        hpositiveFrom
          (globalActualInteriorThreshold D N W m cap reserve),
      forwardSpan D.positiveEnumeration k m) ≤
      globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom
          (globalActualInteriorThreshold D N W m cap reserve) +
      enumeratedWindowCount D.positiveEnumeration N W *
        globalActualInteriorAssemblyLoss D N W m cap reserve := by
  classical
  let sources := globalActualInteriorOnlyEligibleSources
    D hgeom hW hscale hpositiveFrom reserve
  let sourceIndex : GlobalActualInteriorEligibleIndex D hgeom hW hscale
      hpositiveFrom
        (globalActualInteriorThreshold D N W m cap reserve) → ℕ :=
    fun source => source.2.1
  let sourceSpan : GlobalActualInteriorEligibleIndex D hgeom hW hscale
      hpositiveFrom
        (globalActualInteriorThreshold D N W m cap reserve) → ℕ :=
    fun source => Erdos260.GapWord.span
      (actualStabilizedInteriorWord D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        (globalActualInteriorThreshold D N W m cap reserve) source.2)
  let loss := globalActualInteriorAssemblyLoss D N W m cap reserve
  have hindexInjective : Function.Injective sourceIndex := by
    simpa only [sourceIndex] using
      (globalActualInteriorEligibleSourceIndex_injective D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom)
        (threshold := globalActualInteriorThreshold D N W m cap reserve))
  have himage : sources.image sourceIndex =
      globalActualInteriorOnlyWindowIndices D hgeom hW hscale
        hpositiveFrom
          (globalActualInteriorThreshold D N W m cap reserve) := by
    simpa only [sources, sourceIndex] using
      globalActualInteriorOnlyEligibleSources_image
        D hgeom hW hscale hpositiveFrom
  have hmassReindex :
      (∑ k ∈ globalActualInteriorOnlyWindowIndices D hgeom hW hscale
          hpositiveFrom
            (globalActualInteriorThreshold D N W m cap reserve),
        forwardSpan D.positiveEnumeration k m) =
      ∑ source ∈ sources,
        forwardSpan D.positiveEnumeration (sourceIndex source) m := by
    rw [← himage]
    exact Finset.sum_image hindexInjective.injOn
  have hpoint : ∀ source ∈ sources,
      forwardSpan D.positiveEnumeration (sourceIndex source) m ≤
        sourceSpan source + loss := by
    intro source hsource
    simpa only [sources, sourceIndex, sourceSpan, loss] using
      globalActualInteriorOnlySource_forwardSpan_le D hw source hsource
  have hsourceSpan : (∑ source ∈ sources, sourceSpan source) ≤
      globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom
          (globalActualInteriorThreshold D N W m cap reserve) := by
    rw [globalActualInteriorEligibleStabilizedMass_eq_sourceSum
      D hgeom hW hscale hpositiveFrom]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ sources)
  have hsourceCard : sources.card ≤
      enumeratedWindowCount D.positiveEnumeration N W := by
    calc
      sources.card ≤ (Finset.univ : Finset
          (GlobalActualInteriorEligibleIndex D hgeom hW hscale
            hpositiveFrom
              (globalActualInteriorThreshold D N W m cap reserve))).card :=
        Finset.card_le_card (Finset.subset_univ sources)
      _ = Fintype.card (GlobalActualInteriorEligibleIndex D hgeom hW hscale
          hpositiveFrom
            (globalActualInteriorThreshold D N W m cap reserve)) := by simp
      _ ≤ Fintype.card ↥(windowIndices D.positiveEnumeration N W) :=
        Fintype.card_le_of_injective
          (globalActualInteriorEligibleIndexToWindow D
            (hgeom := hgeom) (hW := hW) (hscale := hscale)
            (hpositiveFrom := hpositiveFrom)
            (threshold := globalActualInteriorThreshold D N W m cap reserve))
          (globalActualInteriorEligibleIndexToWindow_injective D
            (hgeom := hgeom) (hW := hW) (hscale := hscale)
            (hpositiveFrom := hpositiveFrom)
            (threshold := globalActualInteriorThreshold D N W m cap reserve))
      _ = enumeratedWindowCount D.positiveEnumeration N W := by
        simp only [Fintype.card_coe, card_windowIndices]
  rw [hmassReindex]
  calc
    (∑ source ∈ sources,
        forwardSpan D.positiveEnumeration (sourceIndex source) m) ≤
        ∑ source ∈ sources, (sourceSpan source + loss) :=
      Finset.sum_le_sum hpoint
    _ = (∑ source ∈ sources, sourceSpan source) + sources.card * loss := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
          hpositiveFrom
            (globalActualInteriorThreshold D N W m cap reserve) +
        enumeratedWindowCount D.positiveEnumeration N W * loss :=
      Nat.add_le_add hsourceSpan (Nat.mul_le_mul_right loss hsourceCard)
    _ = _ := rfl

/-- Deep sources in one exact polynomial/code key. -/
noncomputable def globalActualInteriorGraphSources (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} (threshold F : ℕ)
    (representative : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) :
    Finset (GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) := by
  classical
  exact (globalActualInteriorDeepSources D threshold F).filter fun source =>
    globalActualInteriorGraphKey D source =
      globalActualInteriorGraphKey D representative

@[simp]
theorem mem_globalActualInteriorGraphSources_iff (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    {representative source : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold} :
    source ∈ globalActualInteriorGraphSources D threshold F representative ↔
      source.Deep D F ∧
        globalActualInteriorGraphKey D source =
          globalActualInteriorGraphKey D representative := by
  simp [globalActualInteriorGraphSources,
    globalActualInteriorDeepSources]

/-- Common-continuation terminal samples for one global exact graph key. -/
noncomputable def globalActualInteriorTerminalSamples (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} (threshold F : ℕ)
    (representative : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom threshold) : Finset ℕ :=
  (globalActualInteriorGraphSources D threshold F representative).image
    fun source => globalActualInteriorEndpoint D source +
      Erdos260.GapWord.span
        (canonicalActualInteriorFutureWord D source.2 F)

/-- The global graph-source filter is definitionally the exact census fibre. -/
theorem globalActualInteriorGraphSources_eq_censusFibre (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold) :
    globalActualInteriorGraphSources D threshold F representative =
      interiorCensusSourceFibre
        (globalActualInteriorDeepSources D threshold F)
        (globalActualInteriorGraphKey D)
        (globalActualInteriorGraphKey D representative) := by
  rfl

/-- Sources in one exact graph key have a common canonical future word. -/
theorem globalActualInteriorGraphSource_future_eq (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    {source : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold}
    (hsource : source ∈
      globalActualInteriorGraphSources D threshold F representative) :
    canonicalActualInteriorFutureWord D source.2 F =
      canonicalActualInteriorFutureWord D representative.2 F := by
  have hdata := (mem_globalActualInteriorGraphSources_iff D).mp hsource
  have hcode : globalActualInteriorCode D source =
      globalActualInteriorCode D representative :=
    congrArg Prod.snd hdata.2
  have hword : canonicalActualInteriorBlockWord D source.2 =
      canonicalActualInteriorBlockWord D representative.2 := by
    exact congrArg (fun code : GlobalActualInteriorCode => code.1) hcode
  have hband : dyadicFloorBand
        (actualInteriorDenominator D source.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
          threshold source.2.anchor) =
      dyadicFloorBand
        (actualInteriorDenominator D representative.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
          threshold representative.2.anchor) := by
    exact congrArg (fun code : GlobalActualInteriorCode => code.2.1) hcode
  symm
  apply canonicalActualInteriorFutureWord_eq_of_code
    D hw hgeom (hthreshold representative.1) (hthreshold source.1)
      representative.2 source.2 hrepresentativeDeep hdata.1
        hword.symm hband.symm
  simpa only [globalActualInteriorBlockWord,
    globalActualInteriorDenominatorBand] using hshort

/-- Translating all block endpoints by their common future preserves the
number of distinct samples; this is the exact bridge from census frequency
to sampling frequency. -/
theorem globalActualInteriorTerminalSamples_card_eq_endpointFibre
    (D : CarrySeries) {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2)) :
    (globalActualInteriorTerminalSamples D threshold F representative).card =
      (interiorCensusEndpointFibre
        (Source := GlobalActualInteriorBlockSource D hgeom hW hscale
          hpositiveFrom threshold)
        (Graph := GlobalActualInteriorGraphKey)
        (globalActualInteriorDeepSources D threshold F)
        (fun source => globalActualInteriorGraphKey D source)
        (fun source => globalActualInteriorEndpoint D source)
        (globalActualInteriorGraphKey D representative)).card := by
  classical
  let sources := globalActualInteriorGraphSources D threshold F representative
  let futureSpan := Erdos260.GapWord.span
    (canonicalActualInteriorFutureWord D representative.2 F)
  have hfuture : ∀ source ∈ sources,
      canonicalActualInteriorFutureWord D source.2 F =
        canonicalActualInteriorFutureWord D representative.2 F := by
    intro source hsource
    exact globalActualInteriorGraphSource_future_eq D hw hthreshold
      representative hrepresentativeDeep hshort hsource
  have hsamples : globalActualInteriorTerminalSamples
      D threshold F representative =
      (sources.image (globalActualInteriorEndpoint D)).image
        (fun endpoint => endpoint + futureSpan) := by
    ext n
    simp only [globalActualInteriorTerminalSamples, Finset.mem_image]
    constructor
    · rintro ⟨source, hsource, rfl⟩
      refine ⟨globalActualInteriorEndpoint D source,
        ⟨source, hsource, rfl⟩, ?_⟩
      rw [hfuture source hsource]
    · rintro ⟨endpoint, ⟨source, hsource, rfl⟩, rfl⟩
      refine ⟨source, hsource, ?_⟩
      rw [hfuture source hsource]
  rw [hsamples, Finset.card_image_of_injective]
  · dsimp only [sources]
    rw [interiorCensusEndpointFibre,
      ← globalActualInteriorGraphSources_eq_censusFibre D representative]
  · intro left right heq
    exact Nat.add_right_cancel heq

/-- Common interval length of a global exact-graph sample family. -/
noncomputable def globalActualInteriorSampleIntervalLength (D : CarrySeries)
    {N W m cap : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N} {threshold : ℕ}
    (F : ℕ) (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold) : ℕ :=
  actualInteriorSampleIntervalLength W m cap F
    (logarithmicBlockScale D.base 4
      (globalActualInteriorDenominatorBand D representative))

/- Every global terminal sample lies in the same explicit interval. -/
set_option maxHeartbeats 800000 in
theorem globalActualInteriorTerminalSample_bounds (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ globalActualInteriorTerminalSamples
      D threshold F representative) :
    N < n ∧ n ≤ N + globalActualInteriorSampleIntervalLength
      D F representative := by
  classical
  rw [globalActualInteriorTerminalSamples, Finset.mem_image] at hn
  obtain ⟨source, hsource, rfl⟩ := hn
  have hdata := (mem_globalActualInteriorGraphSources_iff D).mp hsource
  have hfuture := globalActualInteriorGraphSource_future_eq
    D hw hthreshold representative hrepresentativeDeep hshort hsource
  have hbounds := canonicalActualInteriorFutureTerminal_bounds
    D hw hgeom (hthreshold source.1) source.2 hdata.1
  have hcode : globalActualInteriorCode D source =
      globalActualInteriorCode D representative :=
    congrArg Prod.snd hdata.2
  have hband : globalActualInteriorDenominatorBand D source =
      globalActualInteriorDenominatorBand D representative := by
    exact congrArg (fun code : GlobalActualInteriorCode => code.2.1) hcode
  have hblockScale : actualInteriorBlockScale D source.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1)
        threshold source.2.anchor =
      logarithmicBlockScale D.base 4
        (globalActualInteriorDenominatorBand D representative) := by
    rw [actualInteriorBlockScale, ← hband]
    rfl
  constructor
  · exact hbounds.1
  · rw [hfuture, hblockScale] at hbounds
    rw [hfuture]
    rw [globalActualInteriorEndpoint, globalActualInteriorEndpointIndex,
      globalActualInteriorSampleIntervalLength,
      actualInteriorSampleIntervalLength]
    simpa only [Nat.add_assoc] using hbounds.2

/-- Every global terminal sample is an exact carry value of the transformed
representative graph. -/
theorem globalActualInteriorTerminalSample_eval (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ globalActualInteriorTerminalSamples
      D threshold F representative) :
    (((canonicalActualInteriorBlockEndGraph D representative.2).transformWord
      D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorFutureWord D representative.2 F)).poly.eval
          (n : ℚ)) = (D.carry n : ℚ) := by
  classical
  rw [globalActualInteriorTerminalSamples, Finset.mem_image] at hn
  obtain ⟨source, hsource, rfl⟩ := hn
  have hdata := (mem_globalActualInteriorGraphSources_iff D).mp hsource
  have hfuture := globalActualInteriorGraphSource_future_eq
    D hw hthreshold representative hrepresentativeDeep hshort hsource
  have hpoly : (canonicalActualInteriorBlockEndGraph D source.2).poly =
      (canonicalActualInteriorBlockEndGraph D representative.2).poly :=
    congrArg Prod.fst hdata.2
  have htransform := PolynomialGraph.transformWord_poly_eq_of_poly_eq
    hpoly D.base D.denominator D.weight le_rfl
      (canonicalActualInteriorFutureWord D representative.2 F)
  have hfit : ∀ x ∈ realizedPrefixAnchors D N W m
      (lockingThreshold D N) source.1.1,
      (canonicalLockedGraph D hgeom hW hscale hpositiveFrom source.1).poly.eval
          ((x + Erdos260.GapWord.span source.1.1 : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span source.1.1) : ℚ) := by
    intro x hx
    simpa only [Nat.cast_add] using
      canonicalLockedGraph_fit D hgeom hW hscale hpositiveFrom source.1 x hx
  have heval := canonicalActualInteriorFutureGraph_eval_carry
    D (F := F) hfit source.2
  rw [← htransform]
  simpa only [hfuture, globalActualInteriorEndpoint,
    globalActualInteriorEndpointIndex] using heval

/-- Uniform carry-height bound on a global terminal sample. -/
theorem globalActualInteriorTerminalSample_carry_bound (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ globalActualInteriorTerminalSamples
      D threshold F representative) :
    (D.carry n).natAbs ≤ D.actualInteriorSampleHeight N
      (globalActualInteriorSampleIntervalLength D F representative) := by
  have hbounds := globalActualInteriorTerminalSample_bounds
    D hw hthreshold representative hrepresentativeDeep hshort hn
  have hcarry := D.carry_natAbs_le
    (hpositiveFrom.trans hbounds.1.le)
  have hpow : (n + 1) ^ D.weight.natDegree ≤
      (N + globalActualInteriorSampleIntervalLength D F representative + 1) ^
        D.weight.natDegree :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hbounds.2 1) _
  exact hcarry.trans (Nat.mul_le_mul_left D.heightNatConstant hpow)

/-- Real-polynomial bound needed by the global sampling argument. -/
theorem globalActualInteriorTerminalSample_real_bound (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ globalActualInteriorTerminalSamples
      D threshold F representative) :
    |(((canonicalActualInteriorBlockEndGraph D representative.2).transformWord
      D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorFutureWord D representative.2 F)).realPoly.eval
          (n : ℝ))| ≤
      (D.actualInteriorSampleHeight N
        (globalActualInteriorSampleIntervalLength D F representative) : ℕ) := by
  let T := (canonicalActualInteriorBlockEndGraph D representative.2).transformWord
    D.base D.denominator D.weight le_rfl
      (canonicalActualInteriorFutureWord D representative.2 F)
  have heval := globalActualInteriorTerminalSample_eval
    D hw hthreshold representative hrepresentativeDeep hshort hn
  have hmap : T.realPoly.eval (n : ℝ) =
      ((T.poly.eval (n : ℚ) : ℚ) : ℝ) := by
    unfold PolynomialGraph.realPoly
    simpa using Polynomial.eval_map_apply
      (p := T.poly) (f := algebraMap ℚ ℝ) (n : ℚ)
  rw [show (((canonicalActualInteriorBlockEndGraph D representative.2).transformWord
      D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorFutureWord D representative.2 F)).realPoly.eval
          (n : ℝ)) = T.realPoly.eval (n : ℝ) by rfl,
    hmap]
  change |(((T.poly.eval (n : ℚ) : ℚ) : ℝ))| ≤ _
  rw [show T.poly.eval (n : ℚ) = (D.carry n : ℚ) by
    simpa only [T] using heval]
  rw [show |(((D.carry n : ℚ) : ℚ) : ℝ)| =
      ((D.carry n).natAbs : ℝ) by norm_num]
  exact_mod_cast globalActualInteriorTerminalSample_carry_bound
    D hw hthreshold representative hrepresentativeDeep hshort hn

/-- Integral-fibre bound for a global exact-graph sample family. -/
theorem globalActualInteriorTerminalSamples_card_bound (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    (hquot : 0 <
      actualInteriorDenominator D representative.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
          threshold representative.2.anchor /
        (D.denominator *
          (D.weight.coeff D.weight.natDegree).natAbs)) :
    let Hlen := globalActualInteriorSampleIntervalLength D F representative
    let samples := globalActualInteriorTerminalSamples
      D threshold F representative
    (samples.card : ℝ) ≤ D.weight.natDegree +
      D.weight.natDegree * Hlen /
        (((actualInteriorDenominator D representative.1.1
            (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
            threshold representative.2.anchor /
          (D.denominator *
            (D.weight.coeff D.weight.natDegree).natAbs) : ℕ) : ℝ)) ^
              ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹) := by
  let future := canonicalActualInteriorFutureWord D representative.2 F
  let T := (canonicalActualInteriorBlockEndGraph D representative.2).transformWord
    D.base D.denominator D.weight le_rfl future
  let Hlen := globalActualInteriorSampleIntervalLength D F representative
  let samples := globalActualInteriorTerminalSamples
    D threshold F representative
  have hstate : InteriorState D.base
      (((T.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) := by
    simpa only [T, future] using
      canonicalActualInteriorFutureGraph_interiorState
        D hw representative.2
  have hden : (T.normalizedTopState D.denominator D.weight).den =
      actualInteriorDenominator D representative.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
        threshold representative.2.anchor := by
    simpa only [T, future] using
      canonicalActualInteriorFutureGraph_state_den
        D hw hgeom (hthreshold representative.1) representative.2
  have hsamples : ∀ n ∈ samples, N ≤ n ∧ n ≤ N + Hlen := by
    intro n hn
    have hb := globalActualInteriorTerminalSample_bounds
      D hw hthreshold representative hrepresentativeDeep hshort hn
    exact ⟨hb.1.le, by simpa only [Hlen] using hb.2⟩
  have hvalues : ∀ n ∈ samples, ∃ z : ℤ,
      T.poly.eval (n : ℚ) = (z : ℚ) := by
    intro n hn
    refine ⟨D.carry n, ?_⟩
    simpa only [T, future, samples] using
      globalActualInteriorTerminalSample_eval
        D hw hthreshold representative hrepresentativeDeep hshort hn
  have hquotT : 0 < (T.normalizedTopState
      D.denominator D.weight).den /
        (D.denominator *
          (D.weight.coeff D.weight.natDegree).natAbs) := by
    simpa only [hden] using hquot
  have hbound := T.interiorSamples_card_bound hd D.base_ge_two
    D.denominator_pos D.weight hw hstate samples hsamples hvalues hquotT
  simpa only [Hlen, samples, hden] using hbound

/-- Common interval length expressed only through a block/band code. -/
def globalActualInteriorCodeIntervalLength (D : CarrySeries)
    (W m cap F : ℕ) (code : GlobalActualInteriorCode) : ℕ :=
  actualInteriorSampleIntervalLength W m cap F
    (logarithmicBlockScale D.base 4 code.2.1)

/-- Window-level cap for every realized sample interval. -/
def globalActualInteriorSampleIntervalCap (D : CarrySeries)
    (N W m cap F : ℕ) : ℕ :=
  W + m * cap + F + globalActualInteriorBlockScaleCap D N W cap

/-- The interval length attached to any realized source code is bounded by the
single window-level interval cap. -/
theorem globalActualInteriorCodeIntervalLength_le_cap (D : CarrySeries)
    {N W m cap F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (reserve : ℕ)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    globalActualInteriorCodeIntervalLength D W m cap F
        (globalActualInteriorCode D source) ≤
      globalActualInteriorSampleIntervalCap D N W m cap F := by
  have hell := globalActualInteriorBlockScale_le_cap D hw reserve source
  unfold actualInteriorBlockScale at hell
  dsimp only [globalActualInteriorCodeIntervalLength,
    globalActualInteriorSampleIntervalCap, actualInteriorSampleIntervalLength,
    globalActualInteriorCode, globalActualInteriorDenominatorBand,
    globalActualInteriorBlockWord, actualInteriorBlockScale]
  simpa only [Nat.add_assoc] using Nat.add_le_add_left hell (W + m * cap + F)

/-- Uniform lower denominator available from a dyadic band after removing
the fixed normalization factor. -/
def globalActualInteriorEffectiveBandDenominator (D : CarrySeries)
    (code : GlobalActualInteriorCode) : ℕ :=
  max 1 (code.2.1 /
    (D.denominator * (D.weight.coeff D.weight.natDegree).natAbs))

/-- Code-level real endpoint envelope supplied by the integral-fibre bound. -/
noncomputable def globalActualInteriorEndpointEnvelope (D : CarrySeries)
    (W m cap F : ℕ) (code : GlobalActualInteriorCode) : ℝ :=
  D.weight.natDegree +
    D.weight.natDegree *
      globalActualInteriorCodeIntervalLength D W m cap F code /
        (globalActualInteriorEffectiveBandDenominator D code : ℝ) ^
          ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹)

/-- Natural endpoint cap used by the finite interior census. -/
noncomputable def globalActualInteriorEndpointCap (D : CarrySeries)
    (W m cap F : ℕ) (code : GlobalActualInteriorCode) : ℕ :=
  Nat.ceil (globalActualInteriorEndpointEnvelope D W m cap F code)

/-- Endpoint envelope specialized to a high-frequency fibre.  The lower
frequency cutoff absorbs the additive degree term in the integral-fibre
estimate. -/
noncomputable def globalActualInteriorHighEndpointEnvelope (D : CarrySeries)
    (W m cap F : ℕ) (code : GlobalActualInteriorCode) : ℝ :=
  2 * D.weight.natDegree *
      (globalActualInteriorCodeIntervalLength D W m cap F code + 1) /
    (globalActualInteriorEffectiveBandDenominator D code : ℝ) ^
      ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹)

/-- Natural cap associated with the high-frequency endpoint envelope. -/
noncomputable def globalActualInteriorHighEndpointCap (D : CarrySeries)
    (W m cap F : ℕ) (code : GlobalActualInteriorCode) : ℕ :=
  Nat.ceil (globalActualInteriorHighEndpointEnvelope D W m cap F code)

/-- Code-level upper span of one retained greedy block. -/
def globalActualInteriorBlockCap (D : CarrySeries)
    (code : GlobalActualInteriorCode) : ℕ :=
  4 * logarithmicBlockScale D.base 4 code.2.1

/-- The exact endpoint fibre of one realized graph key is bounded by the
code-level natural cap. -/
theorem globalActualInteriorEndpointFibre_card_le_cap (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    (hquot : 0 <
      actualInteriorDenominator D representative.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
          threshold representative.2.anchor /
        (D.denominator *
          (D.weight.coeff D.weight.natDegree).natAbs)) :
    (interiorCensusEndpointFibre
      (globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F)
      (globalActualInteriorGraphKey D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorEndpoint D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorGraphKey D representative)).card ≤
        globalActualInteriorEndpointCap D W m cap F
          (globalActualInteriorCode D representative) := by
  let code := globalActualInteriorCode D representative
  let q := actualInteriorDenominator D representative.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
    threshold representative.2.anchor
  let C := D.denominator *
    (D.weight.coeff D.weight.natDegree).natAbs
  let qeff := q / C
  let Deff := globalActualInteriorEffectiveBandDenominator D code
  let Hlen := globalActualInteriorSampleIntervalLength D F representative
  let sigma : ℝ := (vandermondeExponent D.weight.natDegree : ℝ)⁻¹
  have hbandLe : globalActualInteriorDenominatorBand D representative ≤ q := by
    simpa only [globalActualInteriorDenominatorBand, q] using
      (actualInteriorDenominator_band D hw hgeom representative.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
        threshold (hthreshold representative.1) representative.2.anchor).1
  have hDeff : Deff ≤ qeff := by
    have hone : 1 ≤ qeff := by
      change 0 < qeff
      simpa only [qeff, q, C] using hquot
    have hdiv : globalActualInteriorDenominatorBand D representative / C ≤
        q / C := Nat.div_le_div_right hbandLe
    change max 1 (globalActualInteriorDenominatorBand D representative / C) ≤
      qeff
    exact max_le hone (by simpa only [qeff] using hdiv)
  have hDeffPos : 0 < Deff := by
    dsimp only [Deff, globalActualInteriorEffectiveBandDenominator]
    omega
  have hsigma : 0 ≤ sigma := by
    dsimp only [sigma]
    positivity
  have hpow : (Deff : ℝ) ^ sigma ≤ (qeff : ℝ) ^ sigma := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hDeff
    · exact hsigma
  have hpowPos : 0 < (Deff : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos (by exact_mod_cast hDeffPos) _
  have hfraction :
      (D.weight.natDegree : ℝ) * Hlen / (qeff : ℝ) ^ sigma ≤
        (D.weight.natDegree : ℝ) * Hlen / (Deff : ℝ) ^ sigma := by
    exact div_le_div_of_nonneg_left (by positivity) hpowPos hpow
  have hsample := globalActualInteriorTerminalSamples_card_bound
    D hd hw hthreshold representative hrepresentativeDeep hshort hquot
  have hinterval : Hlen =
      globalActualInteriorCodeIntervalLength D W m cap F code := by
    rfl
  have henvelope :
      ((globalActualInteriorTerminalSamples D threshold F representative).card : ℝ) ≤
        globalActualInteriorEndpointEnvelope D W m cap F code := by
    have hsample' :
        ((globalActualInteriorTerminalSamples D threshold F representative).card : ℝ) ≤
          D.weight.natDegree +
            D.weight.natDegree * Hlen / (qeff : ℝ) ^ sigma := by
      simpa only [Hlen, qeff, q, C, sigma] using hsample
    rw [globalActualInteriorEndpointEnvelope, ← hinterval]
    have hadd := add_le_add_left hfraction (D.weight.natDegree : ℝ)
    exact hsample'.trans (by
      simpa only [add_comm, Deff, sigma] using hadd)
  have hceil :
      (globalActualInteriorTerminalSamples D threshold F representative).card ≤
        globalActualInteriorEndpointCap D W m cap F code := by
    have hreal := henvelope.trans
      (Nat.le_ceil (globalActualInteriorEndpointEnvelope D W m cap F code))
    exact_mod_cast hreal
  rw [← globalActualInteriorTerminalSamples_card_eq_endpointFibre
    D hw hthreshold representative hrepresentativeDeep hshort]
  simpa only [globalActualInteriorEndpointCap, code] using hceil

/-- Total version of the endpoint cap.  If the normalized denominator is
smaller than the fixed coefficient scale, the interval-cardinality bound is
already dominated by the code envelope; otherwise the integral-fibre bound
above applies. -/
theorem globalActualInteriorEndpointFibre_card_le_cap_total (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2)) :
    (interiorCensusEndpointFibre
      (globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F)
      (globalActualInteriorGraphKey D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorEndpoint D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorGraphKey D representative)).card ≤
        globalActualInteriorEndpointCap D W m cap F
          (globalActualInteriorCode D representative) := by
  let q := actualInteriorDenominator D representative.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
    threshold representative.2.anchor
  let C := D.denominator *
    (D.weight.coeff D.weight.natDegree).natAbs
  by_cases hquot : 0 < q / C
  · exact globalActualInteriorEndpointFibre_card_le_cap
      D hd hw hthreshold representative hrepresentativeDeep hshort
        (by simpa only [q, C] using hquot)
  · let code := globalActualInteriorCode D representative
    let Hlen := globalActualInteriorSampleIntervalLength D F representative
    let samples := globalActualInteriorTerminalSamples
      D threshold F representative
    have hquotZero : q / C = 0 := Nat.eq_zero_of_not_pos hquot
    have hbandLe : globalActualInteriorDenominatorBand D representative ≤ q := by
      simpa only [globalActualInteriorDenominatorBand, q] using
        (actualInteriorDenominator_band D hw hgeom representative.1.1
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
          threshold (hthreshold representative.1) representative.2.anchor).1
    have hbandDiv : globalActualInteriorDenominatorBand D representative / C = 0 := by
      have hle := Nat.div_le_div_right (c := C) hbandLe
      rw [hquotZero] at hle
      exact Nat.eq_zero_of_le_zero hle
    have hDeff : globalActualInteriorEffectiveBandDenominator D code = 1 := by
      change max 1 (globalActualInteriorDenominatorBand D representative / C) = 1
      rw [hbandDiv]
      simp
    have hsubset : samples ⊆ Finset.Icc N (N + Hlen) := by
      intro n hn
      have hb := globalActualInteriorTerminalSample_bounds
        D hw hthreshold representative hrepresentativeDeep hshort hn
      exact Finset.mem_Icc.mpr
        ⟨hb.1.le, by simpa only [Hlen] using hb.2⟩
    have hsamples : samples.card ≤ Hlen + 1 := by
      calc
        samples.card ≤ (Finset.Icc N (N + Hlen)).card :=
          Finset.card_le_card hsubset
        _ = Hlen + 1 := by
          simp
          omega
    have hinterval : Hlen =
        globalActualInteriorCodeIntervalLength D W m cap F code := by
      rfl
    have hdReal : (1 : ℝ) ≤ D.weight.natDegree := by
      exact_mod_cast hd
    have henvelope : ((Hlen + 1 : ℕ) : ℝ) ≤
        globalActualInteriorEndpointEnvelope D W m cap F code := by
      rw [globalActualInteriorEndpointEnvelope, ← hinterval, hDeff]
      simp only [Nat.cast_add, Nat.cast_one,
        Real.one_rpow, div_one]
      nlinarith [show (0 : ℝ) ≤ Hlen by positivity]
    have hcap : Hlen + 1 ≤
        globalActualInteriorEndpointCap D W m cap F code := by
      have hreal := henvelope.trans
        (Nat.le_ceil (globalActualInteriorEndpointEnvelope D W m cap F code))
      exact_mod_cast hreal
    rw [← globalActualInteriorTerminalSamples_card_eq_endpointFibre
      D hw hthreshold representative hrepresentativeDeep hshort]
    simpa only [samples, code] using hsamples.trans hcap

/-- High-frequency endpoint fibres satisfy the decaying part of the
integral-fibre estimate alone.  The hypothesis `U ≥ 2d+1` absorbs its additive
degree term; the small-denominator branch is covered by the same formula with
effective denominator one. -/
theorem globalActualInteriorEndpointFibre_card_le_high_cap_total
    (D : CarrySeries) {N W m cap threshold F U : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (representative : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (globalActualInteriorBlockWord D representative)) <
        1 / (4 * (globalActualInteriorDenominatorBand D representative : ℝ) ^ 2))
    (hhigh : U ≤ (interiorCensusEndpointFibre
      (globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F)
      (globalActualInteriorGraphKey D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorEndpoint D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorGraphKey D representative)).card) :
    (interiorCensusEndpointFibre
      (globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F)
      (globalActualInteriorGraphKey D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorEndpoint D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorGraphKey D representative)).card ≤
        globalActualInteriorHighEndpointCap D W m cap F
          (globalActualInteriorCode D representative) := by
  let code := globalActualInteriorCode D representative
  let q := actualInteriorDenominator D representative.1.1
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
    threshold representative.2.anchor
  let C := D.denominator *
    (D.weight.coeff D.weight.natDegree).natAbs
  let qeff := q / C
  let Deff := globalActualInteriorEffectiveBandDenominator D code
  let Hlen := globalActualInteriorSampleIntervalLength D F representative
  let samples := globalActualInteriorTerminalSamples D threshold F representative
  let sigma : ℝ := (vandermondeExponent D.weight.natDegree : ℝ)⁻¹
  have hsamplesFibre := globalActualInteriorTerminalSamples_card_eq_endpointFibre
    D hw hthreshold representative hrepresentativeDeep hshort
  have hfrequency : 2 * D.weight.natDegree + 1 ≤ samples.card := by
    rw [hsamplesFibre]
    exact hU.trans hhigh
  have hinterval : Hlen =
      globalActualInteriorCodeIntervalLength D W m cap F code := by
    rfl
  have hbandLe : globalActualInteriorDenominatorBand D representative ≤ q := by
    simpa only [globalActualInteriorDenominatorBand, q] using
      (actualInteriorDenominator_band D hw hgeom representative.1.1
        (canonicalLockedGraph D hgeom hW hscale hpositiveFrom representative.1)
        threshold (hthreshold representative.1) representative.2.anchor).1
  by_cases hquot : 0 < qeff
  · have hDeff : Deff ≤ qeff := by
      have hone : 1 ≤ qeff := hquot
      have hdiv : globalActualInteriorDenominatorBand D representative / C ≤
          q / C := Nat.div_le_div_right hbandLe
      change max 1 (globalActualInteriorDenominatorBand D representative / C) ≤
        qeff
      exact max_le hone (by simpa only [qeff] using hdiv)
    have hDeffPos : 0 < Deff := by
      dsimp only [Deff, globalActualInteriorEffectiveBandDenominator]
      omega
    have hsigma : 0 ≤ sigma := by dsimp only [sigma]; positivity
    have hpow : (Deff : ℝ) ^ sigma ≤ (qeff : ℝ) ^ sigma := by
      apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast hDeff
      · exact hsigma
    have hpowPos : 0 < (Deff : ℝ) ^ sigma :=
      Real.rpow_pos_of_pos (by exact_mod_cast hDeffPos) _
    have hsample := globalActualInteriorTerminalSamples_card_bound
      D hd hw hthreshold representative hrepresentativeDeep hshort
        (by simpa only [qeff, q, C] using hquot)
    have hsample' : (samples.card : ℝ) ≤
        D.weight.natDegree +
          D.weight.natDegree * Hlen / (qeff : ℝ) ^ sigma := by
      simpa only [samples, Hlen, qeff, q, C, sigma] using hsample
    have hfrequencyReal :
        2 * (D.weight.natDegree : ℝ) + 1 ≤ samples.card := by
      exact_mod_cast hfrequency
    have htwice : (samples.card : ℝ) ≤
        2 * (D.weight.natDegree * Hlen / (qeff : ℝ) ^ sigma) := by
      linarith
    have hfraction :
        D.weight.natDegree * Hlen / (qeff : ℝ) ^ sigma ≤
          D.weight.natDegree * (Hlen + 1) / (Deff : ℝ) ^ sigma := by
      calc
        (D.weight.natDegree : ℝ) * Hlen / (qeff : ℝ) ^ sigma ≤
            (D.weight.natDegree : ℝ) * Hlen / (Deff : ℝ) ^ sigma :=
          div_le_div_of_nonneg_left (by positivity) hpowPos hpow
        _ ≤ (D.weight.natDegree : ℝ) * (Hlen + 1) /
            (Deff : ℝ) ^ sigma := by
          apply div_le_div_of_nonneg_right _ hpowPos.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          norm_num
    have henvelope : (samples.card : ℝ) ≤
        globalActualInteriorHighEndpointEnvelope D W m cap F code := by
      rw [globalActualInteriorHighEndpointEnvelope, ← hinterval]
      calc
        (samples.card : ℝ) ≤ 2 *
            ((D.weight.natDegree : ℝ) * (Hlen + 1) /
              (Deff : ℝ) ^ sigma) :=
          htwice.trans (mul_le_mul_of_nonneg_left hfraction (by norm_num))
        _ = 2 * D.weight.natDegree * (Hlen + 1) /
            (globalActualInteriorEffectiveBandDenominator D code : ℝ) ^
              (vandermondeExponent D.weight.natDegree : ℝ)⁻¹ := by
          dsimp only [Deff, sigma]
          ring
    have hceil : samples.card ≤
        globalActualInteriorHighEndpointCap D W m cap F code := by
      have hreal := henvelope.trans
        (Nat.le_ceil (globalActualInteriorHighEndpointEnvelope D W m cap F code))
      exact_mod_cast hreal
    rw [← hsamplesFibre]
    simpa only [globalActualInteriorHighEndpointCap, code] using hceil
  · have hquotZero : qeff = 0 := Nat.eq_zero_of_not_pos hquot
    have hbandDiv : globalActualInteriorDenominatorBand D representative / C = 0 := by
      have hle := Nat.div_le_div_right (c := C) hbandLe
      have hqdivZero : q / C = 0 := by simpa only [qeff] using hquotZero
      rw [hqdivZero] at hle
      exact Nat.eq_zero_of_le_zero hle
    have hDeff : Deff = 1 := by
      change max 1 (globalActualInteriorDenominatorBand D representative / C) = 1
      rw [hbandDiv]
      simp
    have hsubset : samples ⊆ Finset.Icc N (N + Hlen) := by
      intro n hn
      have hb := globalActualInteriorTerminalSample_bounds
        D hw hthreshold representative hrepresentativeDeep hshort hn
      exact Finset.mem_Icc.mpr
        ⟨hb.1.le, by simpa only [Hlen] using hb.2⟩
    have hsamples : samples.card ≤ Hlen + 1 := by
      calc
        samples.card ≤ (Finset.Icc N (N + Hlen)).card :=
          Finset.card_le_card hsubset
        _ = Hlen + 1 := by simp; omega
    have hdReal : (1 : ℝ) ≤ D.weight.natDegree := by exact_mod_cast hd
    have henvelope : ((Hlen + 1 : ℕ) : ℝ) ≤
        globalActualInteriorHighEndpointEnvelope D W m cap F code := by
      have hDeff' :
          globalActualInteriorEffectiveBandDenominator D code = 1 := by
        simpa only [Deff] using hDeff
      rw [globalActualInteriorHighEndpointEnvelope, ← hinterval, hDeff']
      simp only [Nat.cast_add, Nat.cast_one, Real.one_rpow, div_one]
      nlinarith [show (0 : ℝ) ≤ Hlen by positivity]
    have hcap : Hlen + 1 ≤
        globalActualInteriorHighEndpointCap D W m cap F code := by
      have hreal := henvelope.trans
        (Nat.le_ceil (globalActualInteriorHighEndpointEnvelope D W m cap F code))
      exact_mod_cast hreal
    rw [← hsamplesFibre]
    simpa only [samples, code] using hsamples.trans hcap

/-- Explicit size inequality for coalescing two global high-frequency graph
keys with a common block/band code. -/
noncomputable def GlobalActualInteriorCoalescenceSmall (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (left right : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold) : Prop :=
  let future := canonicalActualInteriorFutureWord D left.2 F
  let Hlen := globalActualInteriorSampleIntervalLength D F left
  let Y := D.actualInteriorSampleHeight N Hlen
  let samplesLeft := globalActualInteriorTerminalSamples D threshold F left
  let samplesRight := globalActualInteriorTerminalSamples D threshold F right
  ((polynomialGraphDifferenceCertificate
    ((canonicalActualInteriorBlockEndGraph D left.2).transformWord
      D.base D.denominator D.weight le_rfl future)
    ((canonicalActualInteriorBlockEndGraph D right.2).transformWord
      D.base D.denominator D.weight le_rfl future)).scale : ℝ) *
      (samplingEnvelope D.weight.natDegree Hlen samplesLeft (Y : ℝ) +
        samplingEnvelope D.weight.natDegree Hlen samplesRight (Y : ℝ)) <
    (D.base : ℝ) ^ Erdos260.GapWord.span future

/-- Uniform certificate-scale bound for two transformed global block-end
graphs. -/
theorem globalActualInteriorDifferenceScale_le (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (left right : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold) :
    let future := canonicalActualInteriorFutureWord D left.2 F
    (polynomialGraphDifferenceCertificate
      ((canonicalActualInteriorBlockEndGraph D left.2).transformWord
        D.base D.denominator D.weight le_rfl future)
      ((canonicalActualInteriorBlockEndGraph D right.2).transformWord
        D.base D.denominator D.weight le_rfl future)).scale ≤
      (W + lockingThreshold D N + cap) ^
        (2 * vandermondeExponent D.weight.natDegree) := by
  dsimp only
  apply polynomialGraphDifference_scale_le
  · rw [PolynomialGraph.transformWord_denominator]
    unfold canonicalActualInteriorBlockEndGraph
    rw [PolynomialGraph.transformWord_denominator]
    exact canonicalLockedGraph_den_le
      D hgeom hW hscale hpositiveFrom left.1
  · rw [PolynomialGraph.transformWord_denominator]
    unfold canonicalActualInteriorBlockEndGraph
    rw [PolynomialGraph.transformWord_denominator]
    exact canonicalLockedGraph_den_le
      D hgeom hW hscale hpositiveFrom right.1

/-- Source-independent upper envelope whose domination by `b^F` implies the
actual coalescence-small inequality. -/
noncomputable def globalActualInteriorCoalescenceEnvelope (D : CarrySeries)
    (N W m cap U F : ℕ) (code : GlobalActualInteriorCode) : ℝ :=
  let Hlen := globalActualInteriorCodeIntervalLength D W m cap F code
  let Y := D.actualInteriorSampleHeight N Hlen
  (((W + lockingThreshold D N + cap) ^
      (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) *
    (2 * samplingConstant D.weight.natDegree * (Y : ℝ) *
      (1 + (Hlen : ℝ) / U) ^ D.weight.natDegree)

/-- A source-independent coalescence envelope obtained by replacing the
realized interval and carry height by their common window caps. -/
noncomputable def globalActualInteriorUniformCoalescenceEnvelope
    (D : CarrySeries) (N W m cap U F : ℕ) : ℝ :=
  let Hcap := globalActualInteriorSampleIntervalCap D N W m cap F
  let Ycap := D.actualInteriorSampleHeight N Hcap
  (((W + lockingThreshold D N + cap) ^
      (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) *
    (2 * samplingConstant D.weight.natDegree * (Ycap : ℝ) *
      (1 + (Hcap : ℝ) / U) ^ D.weight.natDegree)

/-- Natural coefficient in the polynomial upper bound for the uniform
coalescence envelope. -/
def globalActualInteriorCoalescencePolynomialConstant
    (D : CarrySeries) : ℕ :=
  (2 * (D.weight.natDegree + 1) *
      (2 * (D.weight.natDegree + 1)) ^ D.weight.natDegree) *
    D.heightNatConstant

/-- Degree of the polynomial upper bound for the uniform coalescence
envelope. -/
def globalActualInteriorCoalescencePolynomialExponent
    (D : CarrySeries) : ℕ :=
  2 * vandermondeExponent D.weight.natDegree +
    2 * D.weight.natDegree

/-- Explicit logarithmic continuation span that dominates the full uniform
coalescence envelope once its sample interval is at most `4N`. -/
def globalActualInteriorContinuationSpan (D : CarrySeries) (N : ℕ) : ℕ :=
  Nat.clog D.base
      (globalActualInteriorCoalescencePolynomialConstant D + 1) +
    globalActualInteriorCoalescencePolynomialExponent D *
      (Nat.log D.base (5 * N + 1) + 1)

/-- The explicit continuation span dominates the source-independent
coalescence envelope.  All hidden polynomial `O` terms of the manuscript are
replaced by the displayed natural coefficient and exponent. -/
theorem globalActualInteriorUniformCoalescenceEnvelope_lt_continuation
    (D : CarrySeries) {N W m cap U F : ℕ}
    (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (hU : 0 < U)
    (hH : globalActualInteriorSampleIntervalCap D N W m cap F ≤ 4 * N) :
    globalActualInteriorUniformCoalescenceEnvelope D N W m cap U F <
      (D.base : ℝ) ^ globalActualInteriorContinuationSpan D N := by
  let Hcap := globalActualInteriorSampleIntervalCap D N W m cap F
  let X := 5 * N + 1
  let C := globalActualInteriorCoalescencePolynomialConstant D
  let a := globalActualInteriorCoalescencePolynomialExponent D
  have hscaleX : W + lockingThreshold D N + cap ≤ X := by
    dsimp only [X]
    omega
  have hheightX : N + Hcap + 1 ≤ X := by
    dsimp only [Hcap, X] at hH ⊢
    omega
  have hratio :
      1 + (Hcap : ℝ) / U ≤ (X : ℝ) := by
    have hUreal : (1 : ℝ) ≤ U := by exact_mod_cast hU
    have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
    have hdiv : (Hcap : ℝ) / U ≤ Hcap := by
      rw [div_le_iff₀ hUpos]
      exact le_mul_of_one_le_right (by positivity) hUreal
    have hHX : 1 + Hcap ≤ (X : ℕ) := by
      dsimp only [Hcap, X] at hH ⊢
      omega
    calc
      1 + (Hcap : ℝ) / U ≤ 1 + Hcap := by linarith
      _ ≤ X := by exact_mod_cast hHX
  have hsamplingCast :
      (2 * samplingConstant D.weight.natDegree : ℝ) =
        (2 * (D.weight.natDegree + 1) *
          (2 * (D.weight.natDegree + 1)) ^ D.weight.natDegree : ℕ) := by
    unfold samplingConstant
    push_cast
    ring
  have hbound :
      globalActualInteriorUniformCoalescenceEnvelope D N W m cap U F ≤
        (C : ℝ) * (X : ℝ) ^ a := by
    unfold globalActualInteriorUniformCoalescenceEnvelope
      CarrySeries.actualInteriorSampleHeight
    dsimp only
    rw [hsamplingCast]
    let S : ℝ := ((2 * (D.weight.natDegree + 1) *
      (2 * (D.weight.natDegree + 1)) ^ D.weight.natDegree : ℕ) : ℝ)
    let Y : ℝ := ((D.heightNatConstant * (N + Hcap + 1) ^
      D.weight.natDegree : ℕ) : ℝ)
    let R : ℝ := (1 + (Hcap : ℝ) / U) ^ D.weight.natDegree
    have hscaleNat :
        (W + lockingThreshold D N + cap) ^
            (2 * vandermondeExponent D.weight.natDegree) ≤
          X ^ (2 * vandermondeExponent D.weight.natDegree) :=
      Nat.pow_le_pow_left hscaleX _
    have hscaleReal :
        (((W + lockingThreshold D N + cap) ^
            (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) ≤
          (X : ℝ) ^ (2 * vandermondeExponent D.weight.natDegree) := by
      exact_mod_cast hscaleNat
    have hheightNat :
        D.heightNatConstant * (N + Hcap + 1) ^ D.weight.natDegree ≤
          D.heightNatConstant * X ^ D.weight.natDegree := by
      gcongr
    have hheightReal :
        Y ≤ (D.heightNatConstant : ℝ) *
          (X : ℝ) ^ D.weight.natDegree := by
      dsimp only [Y]
      exact_mod_cast hheightNat
    have hratioPow : R ≤ (X : ℝ) ^ D.weight.natDegree := by
      exact pow_le_pow_left₀ (by positivity) hratio _
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    have hY : 0 ≤ Y := by dsimp only [Y]; positivity
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    change
      (((W + lockingThreshold D N + cap) ^
            (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) *
          (S * Y * R) ≤
        (C : ℝ) * (X : ℝ) ^ a
    calc
      _ ≤ (X : ℝ) ^ (2 * vandermondeExponent D.weight.natDegree) *
          (S * Y * R) :=
        mul_le_mul_of_nonneg_right hscaleReal
          (mul_nonneg (mul_nonneg hS hY) hR)
      _ ≤ (X : ℝ) ^ (2 * vandermondeExponent D.weight.natDegree) *
          (S * ((D.heightNatConstant : ℝ) *
            (X : ℝ) ^ D.weight.natDegree) * R) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hheightReal hS) hR
      _ ≤ (X : ℝ) ^ (2 * vandermondeExponent D.weight.natDegree) *
          (S * ((D.heightNatConstant : ℝ) *
            (X : ℝ) ^ D.weight.natDegree) *
              (X : ℝ) ^ D.weight.natDegree) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hratioPow
          (mul_nonneg hS (by positivity))
      _ = (C : ℝ) * (X : ℝ) ^ a := by
        dsimp only [S, C, a,
          globalActualInteriorCoalescencePolynomialConstant,
          globalActualInteriorCoalescencePolynomialExponent]
        push_cast
        rw [pow_add]
        ring
  have hpoly := CarrySeries.polynomial_lt_base_pow_logScale
    D.base_ge_two C X a
  have hpolyReal :
      (C : ℝ) * (X : ℝ) ^ a <
        (D.base : ℝ) ^ globalActualInteriorContinuationSpan D N := by
    exact_mod_cast hpoly
  exact hbound.trans_lt hpolyReal

/-- Four elementary window-scale bounds place the canonical sample interval
inside `4N`. -/
theorem globalActualInteriorSampleIntervalCap_le_four_mul
    (D : CarrySeries) {N W m cap F : ℕ}
    (hW : W ≤ N) (hmcap : m * cap ≤ N) (hF : F ≤ N)
    (hell : globalActualInteriorBlockScaleCap D N W cap ≤ N) :
    globalActualInteriorSampleIntervalCap D N W m cap F ≤ 4 * N := by
  unfold globalActualInteriorSampleIntervalCap
  omega

/-- Canonical finite-scale coalescence inequality, with all scale side
conditions exposed as elementary natural inequalities. -/
theorem globalActualInteriorUniformCoalescenceEnvelope_lt_canonical
    (D : CarrySeries) {N W m cap U : ℕ}
    (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (hU : 0 < U)
    (hmcap : m * cap ≤ N)
    (hF : globalActualInteriorContinuationSpan D N ≤ N)
    (hell : globalActualInteriorBlockScaleCap D N W cap ≤ N) :
    globalActualInteriorUniformCoalescenceEnvelope D N W m cap U
        (globalActualInteriorContinuationSpan D N) <
      (D.base : ℝ) ^ globalActualInteriorContinuationSpan D N := by
  apply globalActualInteriorUniformCoalescenceEnvelope_lt_continuation
    D hW hscale hU
  exact globalActualInteriorSampleIntervalCap_le_four_mul
    D hW hmcap hF hell

/-- Every realized source-wise envelope is dominated by the single uniform
window envelope. -/
theorem globalActualInteriorCoalescenceEnvelope_le_uniform (D : CarrySeries)
    {N W m cap U F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (reserve : ℕ)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    globalActualInteriorCoalescenceEnvelope D N W m cap U F
        (globalActualInteriorCode D source) ≤
      globalActualInteriorUniformCoalescenceEnvelope D N W m cap U F := by
  let Hlen := globalActualInteriorCodeIntervalLength D W m cap F
    (globalActualInteriorCode D source)
  let Hcap := globalActualInteriorSampleIntervalCap D N W m cap F
  have hH : Hlen ≤ Hcap := by
    simpa only [Hlen, Hcap] using
      globalActualInteriorCodeIntervalLength_le_cap D hw reserve source
  have hY := D.actualInteriorSampleHeight_mono (N := N) hH
  have hYReal :
      (D.actualInteriorSampleHeight N Hlen : ℝ) ≤
        (D.actualInteriorSampleHeight N Hcap : ℝ) := by
    exact_mod_cast hY
  unfold globalActualInteriorCoalescenceEnvelope
    globalActualInteriorUniformCoalescenceEnvelope
  dsimp only
  gcongr
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (samplingConstant_pos _).le) (by positivity)
  · exact mul_nonneg (by norm_num) (samplingConstant_pos _).le

/-- A single explicit envelope inequality proves the source-specific
coalescence-small condition for every high-frequency pair. -/
theorem globalActualInteriorCoalescenceSmall_of_envelope (D : CarrySeries)
    {N W m cap threshold F U : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (left right : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hleftDeep : left.Deep D F) (hU : 0 < U)
    (hleftCard : U ≤
      (globalActualInteriorTerminalSamples D threshold F left).card)
    (hrightCard : U ≤
      (globalActualInteriorTerminalSamples D threshold F right).card)
    (henvelope : globalActualInteriorCoalescenceEnvelope
      D N W m cap U F (globalActualInteriorCode D left) <
        (D.base : ℝ) ^ F) :
    GlobalActualInteriorCoalescenceSmall D (F := F) left right := by
  let future := canonicalActualInteriorFutureWord D left.2 F
  let Hlen := globalActualInteriorSampleIntervalLength D F left
  let Y := D.actualInteriorSampleHeight N Hlen
  let samplesLeft := globalActualInteriorTerminalSamples D threshold F left
  let samplesRight := globalActualInteriorTerminalSamples D threshold F right
  let common := samplingConstant D.weight.natDegree * (Y : ℝ) *
    (1 + (Hlen : ℝ) / U) ^ D.weight.natDegree
  have hscaleNat := globalActualInteriorDifferenceScale_le
    D (F := F) left right
  have hscaleReal :
      ((polynomialGraphDifferenceCertificate
        ((canonicalActualInteriorBlockEndGraph D left.2).transformWord
          D.base D.denominator D.weight le_rfl future)
        ((canonicalActualInteriorBlockEndGraph D right.2).transformWord
          D.base D.denominator D.weight le_rfl future)).scale : ℝ) ≤
        (((W + lockingThreshold D N + cap) ^
          (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) := by
    exact_mod_cast (by simpa only [future] using hscaleNat)
  have hleftEnvelope :
      samplingEnvelope D.weight.natDegree Hlen samplesLeft (Y : ℝ) ≤
        common := by
    simpa only [common] using samplingEnvelope_le_of_card_ge
      samplesLeft (by positivity) hU (by simpa only [samplesLeft] using hleftCard)
  have hrightEnvelope :
      samplingEnvelope D.weight.natDegree Hlen samplesRight (Y : ℝ) ≤
        common := by
    simpa only [common] using samplingEnvelope_le_of_card_ge
      samplesRight (by positivity) hU (by simpa only [samplesRight] using hrightCard)
  have hsum :
      samplingEnvelope D.weight.natDegree Hlen samplesLeft (Y : ℝ) +
          samplingEnvelope D.weight.natDegree Hlen samplesRight (Y : ℝ) ≤
        2 * common := by
    linarith
  have hsumNonneg :
      0 ≤ samplingEnvelope D.weight.natDegree Hlen samplesLeft (Y : ℝ) +
          samplingEnvelope D.weight.natDegree Hlen samplesRight (Y : ℝ) := by
    exact add_nonneg
      (samplingEnvelope_nonneg _ _ _ (by positivity))
      (samplingEnvelope_nonneg _ _ _ (by positivity))
  have hscaleCapNonneg :
      0 ≤ (((W + lockingThreshold D N + cap) ^
        (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) := by
    positivity
  have hinterval : Hlen = globalActualInteriorCodeIntervalLength
      D W m cap F (globalActualInteriorCode D left) := by
    rfl
  have henvelope' :
      (((W + lockingThreshold D N + cap) ^
          (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) *
          (2 * common) < (D.base : ℝ) ^ F := by
    simpa only [globalActualInteriorCoalescenceEnvelope,
      ← hinterval, Y, common, mul_assoc] using henvelope
  have hfuture := (canonicalActualInteriorFutureWord_bounds
    D hw hgeom (hthreshold left.1) left.2 hleftDeep).2.1
  have hbase : (1 : ℝ) < D.base := by
    exact_mod_cast (show 1 < D.base from lt_of_lt_of_le (by omega) D.base_ge_two)
  change
    ((polynomialGraphDifferenceCertificate
      ((canonicalActualInteriorBlockEndGraph D left.2).transformWord
        D.base D.denominator D.weight le_rfl future)
      ((canonicalActualInteriorBlockEndGraph D right.2).transformWord
        D.base D.denominator D.weight le_rfl future)).scale : ℝ) *
        (samplingEnvelope D.weight.natDegree Hlen samplesLeft (Y : ℝ) +
          samplingEnvelope D.weight.natDegree Hlen samplesRight (Y : ℝ)) <
      (D.base : ℝ) ^ Erdos260.GapWord.span future
  calc
    _ ≤ (((W + lockingThreshold D N + cap) ^
          (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) *
        (samplingEnvelope D.weight.natDegree Hlen samplesLeft (Y : ℝ) +
          samplingEnvelope D.weight.natDegree Hlen samplesRight (Y : ℝ)) :=
      mul_le_mul_of_nonneg_right hscaleReal hsumNonneg
    _ ≤ (((W + lockingThreshold D N + cap) ^
          (2 * vandermondeExponent D.weight.natDegree) : ℕ) : ℝ) *
        (2 * common) := mul_le_mul_of_nonneg_left hsum hscaleCapNonneg
    _ < (D.base : ℝ) ^ F := henvelope'
    _ < (D.base : ℝ) ^ Erdos260.GapWord.span future :=
      pow_lt_pow_right₀ hbase hfuture

/-- Global high-frequency coalescence.  Unlike the local spike, its sample
sets may contain sources from many locking-prefix fibres; the proved global
endpoint/future bridge supplies the required common interval and values. -/
theorem globalHighFrequencyGraphKeys_coalesce (D : CarrySeries)
    {N W m cap threshold F : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (left right : GlobalActualInteriorBlockSource
      D hgeom hW hscale hpositiveFrom threshold)
    (hleftDeep : left.Deep D F) (hrightDeep : right.Deep D F)
    (hcode : globalActualInteriorCode D left =
      globalActualInteriorCode D right)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span (globalActualInteriorBlockWord D left)) <
        1 / (4 * (globalActualInteriorDenominatorBand D left : ℝ) ^ 2))
    (hinterval : D.weight.natDegree ≤
      globalActualInteriorSampleIntervalLength D F left)
    (hleftFrequency : 2 * D.weight.natDegree + 1 ≤
      (globalActualInteriorTerminalSamples D threshold F left).card)
    (hrightFrequency : 2 * D.weight.natDegree + 1 ≤
      (globalActualInteriorTerminalSamples D threshold F right).card)
    (hsmall : GlobalActualInteriorCoalescenceSmall D (F := F) left right) :
    globalActualInteriorGraphKey D left =
      globalActualInteriorGraphKey D right := by
  let future := canonicalActualInteriorFutureWord D left.2 F
  let Hlen := globalActualInteriorSampleIntervalLength D F left
  let Y := D.actualInteriorSampleHeight N Hlen
  let samplesLeft := globalActualInteriorTerminalSamples D threshold F left
  let samplesRight := globalActualInteriorTerminalSamples D threshold F right
  have hword : canonicalActualInteriorBlockWord D left.2 =
      canonicalActualInteriorBlockWord D right.2 :=
    congrArg (fun code : GlobalActualInteriorCode => code.1) hcode
  have hband : globalActualInteriorDenominatorBand D left =
      globalActualInteriorDenominatorBand D right :=
    congrArg (fun code : GlobalActualInteriorCode => code.2.1) hcode
  have hfuture : canonicalActualInteriorFutureWord D left.2 F =
      canonicalActualInteriorFutureWord D right.2 F := by
    apply canonicalActualInteriorFutureWord_eq_of_code
      D hw hgeom (hthreshold left.1) (hthreshold right.1)
        left.2 right.2 hleftDeep hrightDeep hword
    · simpa only [globalActualInteriorDenominatorBand] using hband
    · simpa only [globalActualInteriorBlockWord,
        globalActualInteriorDenominatorBand] using hshort
  have hHlen : globalActualInteriorSampleIntervalLength D F right = Hlen := by
    dsimp only [Hlen, globalActualInteriorSampleIntervalLength]
    rw [← hband]
  have hshortRight :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span (globalActualInteriorBlockWord D right)) <
        1 / (4 * (globalActualInteriorDenominatorBand D right : ℝ) ^ 2) := by
    simpa only [← hword, ← hband,
      globalActualInteriorBlockWord] using hshort
  have hsamplesLeft : ∀ n ∈ samplesLeft,
      N ≤ n ∧ n ≤ N + Hlen := by
    intro n hn
    have hb := globalActualInteriorTerminalSample_bounds
      D hw hthreshold left hleftDeep hshort hn
    exact ⟨hb.1.le, by simpa only [Hlen] using hb.2⟩
  have hsamplesRight : ∀ n ∈ samplesRight,
      N ≤ n ∧ n ≤ N + Hlen := by
    intro n hn
    have hb := globalActualInteriorTerminalSample_bounds
      D hw hthreshold right hrightDeep hshortRight hn
    exact ⟨hb.1.le, by simpa only [hHlen] using hb.2⟩
  have hvaluesLeft : ∀ n ∈ samplesLeft,
      |(((canonicalActualInteriorBlockEndGraph D left.2).transformWord
        D.base D.denominator D.weight le_rfl future).realPoly.eval (n : ℝ))| ≤
          (Y : ℝ) := by
    intro n hn
    simpa only [future, Y, Hlen, samplesLeft] using
      globalActualInteriorTerminalSample_real_bound
        D hw hthreshold left hleftDeep hshort hn
  have hvaluesRight : ∀ n ∈ samplesRight,
      |(((canonicalActualInteriorBlockEndGraph D right.2).transformWord
        D.base D.denominator D.weight le_rfl future).realPoly.eval (n : ℝ))| ≤
          (Y : ℝ) := by
    intro n hn
    have hb := globalActualInteriorTerminalSample_real_bound
      D hw hthreshold right hrightDeep hshortRight hn
    simpa only [future, hfuture, Y, Hlen, hHlen, samplesRight] using hb
  have hpoly : (canonicalActualInteriorBlockEndGraph D left.2).poly =
      (canonicalActualInteriorBlockEndGraph D right.2).poly := by
    apply lem_coalescence (A := N) (Hlen := Hlen) (b := D.base)
      (F := Erdos260.GapWord.span future) (Q := D.denominator)
      (Y₁ := (Y : ℝ)) (Y₂ := (Y : ℝ))
      (by simpa only [Hlen] using hinterval) D.base_ge_two
      (canonicalActualInteriorBlockEndGraph D left.2)
      (canonicalActualInteriorBlockEndGraph D right.2)
      D.weight le_rfl future rfl samplesLeft samplesRight
    · simpa only [samplesLeft] using hleftFrequency
    · simpa only [samplesRight] using hrightFrequency
    · exact hsamplesLeft
    · exact hsamplesRight
    · positivity
    · positivity
    · exact hvaluesLeft
    · exact hvaluesRight
    · simpa only [GlobalActualInteriorCoalescenceSmall,
        future, Hlen, Y, samplesLeft, samplesRight] using hsmall
  exact Prod.ext hpoly hcode

/-! ## Actual global interior census -/

/-- The manuscript's interior proposition instantiated on the genuine global
source family.  One source-wise, code-level envelope replaces the former
pairwise coalescence hypothesis; all source maps, cells, graph keys, endpoint
fibres, and coalescence maps are the canonical objects constructed above. -/
theorem globalActual_prop_interior (D : CarrySeries)
    {N W m cap threshold F U : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hthreshold : ∀ pfx : CanonicalNonrarePrefix
        D N W m (lockingThreshold D N),
      Nat.log 2 (PolynomialGraph.normalizedTopState
          (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx)
          D.denominator D.weight).den + cap ≤ threshold)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : ∀ source ∈ globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F,
      globalActualInteriorCoalescenceEnvelope
        D N W m cap U F (globalActualInteriorCode D source) <
          (D.base : ℝ) ^ F) :
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    let graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let codeOf : GlobalActualInteriorGraphKey → GlobalActualInteriorCode :=
      Prod.snd
    let endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let span := globalActualInteriorBlockSpan D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    ∑ source ∈ sources, span source ≤
      (∑ graph ∈ interiorCensusGraphKeys sources graphOf,
        if ¬ InteriorCensusHigh sources graphOf endpoint U graph then
          U * (m + 1) * globalActualInteriorBlockCap D (codeOf graph)
        else 0) +
      ∑ code ∈ interiorCensusHighCodeKeys
          sources graphOf codeOf endpoint U,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code := by
  classical
  dsimp only
  apply prop_interior
    (sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F)
    (graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom))
    (codeOf := fun graph : GlobalActualInteriorGraphKey => graph.2)
    (endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom))
    (offset := globalActualInteriorOffset D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom))
    (span := globalActualInteriorBlockSpan D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom))
    (blockCap := globalActualInteriorBlockCap D)
    (endpointCap := globalActualInteriorHighEndpointCap D W m cap F)
    (U := U)
  · exact globalActualInteriorEndpointOffset_injective D
  · intro source hsource
    simpa only [globalActualInteriorBlockCap,
      globalActualInteriorGraphKey, globalActualInteriorCode] using
      globalActualInteriorBlockSpan_le D hw hthreshold source
  · intro graph hgraph hhigh
    rcases Finset.mem_image.mp hgraph with ⟨source, hsource, rfl⟩
    have hdeep : source.Deep D F := by
      exact (Finset.mem_filter.mp hsource).2
    have hsep := globalActualInterior_short_separation
      D hw hthreshold source
    simpa only [globalActualInteriorGraphKey] using
      globalActualInteriorEndpointFibre_card_le_high_cap_total
        D hd hw hthreshold hU source hdeep hsep hhigh
  · intro left hleft hleftHigh right hright hrightHigh hcode
    rcases Finset.mem_image.mp hleft with
      ⟨leftSource, hleftSource, rfl⟩
    rcases Finset.mem_image.mp hright with
      ⟨rightSource, hrightSource, rfl⟩
    have hleftDeep : leftSource.Deep D F :=
      (Finset.mem_filter.mp hleftSource).2
    have hrightDeep : rightSource.Deep D F :=
      (Finset.mem_filter.mp hrightSource).2
    have hcode' : globalActualInteriorCode D leftSource =
        globalActualInteriorCode D rightSource := by
      simpa only [globalActualInteriorGraphKey] using hcode
    have hleftSep := globalActualInterior_short_separation
      D hw hthreshold leftSource
    have hrightSep := globalActualInterior_short_separation
      D hw hthreshold rightSource
    have hleftCard :=
      globalActualInteriorTerminalSamples_card_eq_endpointFibre
        D hw hthreshold leftSource hleftDeep
          hleftSep
    have hrightCard :=
      globalActualInteriorTerminalSamples_card_eq_endpointFibre
        D hw hthreshold rightSource hrightDeep
          hrightSep
    have hleftFrequency : 2 * D.weight.natDegree + 1 ≤
        (globalActualInteriorTerminalSamples D threshold F leftSource).card := by
      rw [hleftCard]
      exact hU.trans hleftHigh
    have hrightFrequency : 2 * D.weight.natDegree + 1 ≤
        (globalActualInteriorTerminalSamples D threshold F rightSource).card := by
      rw [hrightCard]
      exact hU.trans hrightHigh
    have hleftU : U ≤
        (globalActualInteriorTerminalSamples D threshold F leftSource).card := by
      rw [hleftCard]
      exact hleftHigh
    have hrightU : U ≤
        (globalActualInteriorTerminalSamples D threshold F rightSource).card := by
      rw [hrightCard]
      exact hrightHigh
    have hintervalLeft : D.weight.natDegree ≤
        globalActualInteriorSampleIntervalLength D F leftSource := by
      unfold globalActualInteriorSampleIntervalLength
        actualInteriorSampleIntervalLength
      omega
    exact globalHighFrequencyGraphKeys_coalesce
      D hw hthreshold leftSource rightSource hleftDeep hrightDeep hcode'
        hleftSep hintervalLeft
        hleftFrequency hrightFrequency
        (globalActualInteriorCoalescenceSmall_of_envelope
          D hw hthreshold leftSource rightSource hleftDeep (by omega)
            hleftU hrightU (henvelope leftSource hleftSource))

/-- Canonical-threshold form of the genuine global interior proposition.  Its
only remaining coalescence hypothesis is one source-independent numerical
inequality. -/
theorem globalActual_prop_interior_of_uniform_envelope (D : CarrySeries)
    {N W m cap F U : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (reserve : ℕ)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : globalActualInteriorUniformCoalescenceEnvelope
      D N W m cap U F < (D.base : ℝ) ^ F) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    let graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let codeOf : GlobalActualInteriorGraphKey → GlobalActualInteriorCode :=
      Prod.snd
    let endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let span := globalActualInteriorBlockSpan D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    ∑ source ∈ sources, span source ≤
      (∑ graph ∈ interiorCensusGraphKeys sources graphOf,
        if ¬ InteriorCensusHigh sources graphOf endpoint U graph then
          U * (m + 1) * globalActualInteriorBlockCap D (codeOf graph)
        else 0) +
      ∑ code ∈ interiorCensusHighCodeKeys
          sources graphOf codeOf endpoint U,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code := by
  dsimp only
  apply globalActual_prop_interior D hd hw
    (fun pfx => globalActualInteriorThreshold_covers
      D hgeom hW hscale hpositiveFrom hw reserve pfx) hU hF
  intro source hsource
  exact (globalActualInteriorCoalescenceEnvelope_le_uniform
    D hw reserve source).trans_lt henvelope

/-! ## Uniform bounds for the two interior census sums -/

/-- At the canonical threshold, the block cap carried by every realized graph
key is bounded by one window-level logarithmic scale. -/
theorem globalActualInteriorBlockCap_le_uniform (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    globalActualInteriorBlockCap D (globalActualInteriorCode D source) ≤
      4 * globalActualInteriorBlockScaleCap D N W cap := by
  unfold globalActualInteriorBlockCap globalActualInteriorCode
    globalActualInteriorBlockScaleCap globalActualInteriorDenominatorBand
    actualInteriorBlockScale
  exact Nat.mul_le_mul_left 4
    (globalActualInteriorBlockScale_le_cap D hw reserve source)

/-- Codes with one fixed pair of dyadic band exponents. -/
noncomputable def globalActualInteriorCodeBand (D : CarrySeries)
    (reserve eD eZ : ℕ) : Finset GlobalActualInteriorCode := by
  classical
  exact if reserve < 2 * 2 ^ eZ ∧ D.base ^ (2 ^ eZ) < 4 * 2 ^ eD then
    (retainedBlockWords
      (logarithmicBlockScale D.base 4 (2 ^ eD)) (2 ^ eZ)).image
        fun word => (word, 2 ^ eD, 2 ^ eZ)
  else ∅

/-- All mean-gap bands attached to one denominator-band exponent. -/
noncomputable def globalActualInteriorCodeSlice (D : CarrySeries)
    (cap reserve eD : ℕ) : Finset GlobalActualInteriorCode := by
  classical
  exact (Finset.range (Nat.log 2 cap + 1)).biUnion
    (globalActualInteriorCodeBand D reserve eD)

/-- Finite ambient code family for one canonical window.  Both band
coordinates are represented by their dyadic exponents; the reserve filter
keeps exactly the mean-gap range relevant to the retained interior census. -/
noncomputable def globalActualInteriorCodeUniverse (D : CarrySeries)
    (N W cap reserve : ℕ) : Finset GlobalActualInteriorCode := by
  classical
  exact (Finset.range
      (Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1)).biUnion
    (globalActualInteriorCodeSlice D cap reserve)

theorem globalActualInteriorCodeBand_coordinates (D : CarrySeries)
    {reserve eD eZ : ℕ} {code : GlobalActualInteriorCode}
    (hcode : code ∈ globalActualInteriorCodeBand D reserve eD eZ) :
    code.2.1 = 2 ^ eD ∧ code.2.2 = 2 ^ eZ := by
  classical
  by_cases hband : reserve < 2 * 2 ^ eZ ∧
      D.base ^ (2 ^ eZ) < 4 * 2 ^ eD
  · rw [globalActualInteriorCodeBand, if_pos hband,
      Finset.mem_image] at hcode
    rcases hcode with ⟨word, _hword, hword⟩
    subst code
    exact ⟨rfl, rfl⟩
  · simp [globalActualInteriorCodeBand, hband] at hcode

theorem globalActualInteriorCodeBand_disjoint_of_ne (D : CarrySeries)
    (reserve eD : ℕ) {left right : ℕ} (hne : left ≠ right) :
    Disjoint (globalActualInteriorCodeBand D reserve eD left)
      (globalActualInteriorCodeBand D reserve eD right) := by
  classical
  rw [Finset.disjoint_left]
  intro code hleft hright
  have hpows : 2 ^ left = 2 ^ right :=
    (globalActualInteriorCodeBand_coordinates D hleft).2.symm.trans
      (globalActualInteriorCodeBand_coordinates D hright).2
  exact hne (Nat.pow_right_injective (by norm_num) hpows)

theorem globalActualInteriorCodeSlice_pairwiseDisjoint (D : CarrySeries)
    (cap reserve eD : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (Nat.log 2 cap + 1)))
      (globalActualInteriorCodeBand D reserve eD) := by
  intro left _hleft right _hright hne
  exact globalActualInteriorCodeBand_disjoint_of_ne D reserve eD hne

theorem globalActualInteriorCodeSlice_disjoint_of_ne (D : CarrySeries)
    (cap reserve : ℕ) {left right : ℕ} (hne : left ≠ right) :
    Disjoint (globalActualInteriorCodeSlice D cap reserve left)
      (globalActualInteriorCodeSlice D cap reserve right) := by
  classical
  rw [Finset.disjoint_left]
  intro code hleft hright
  rw [globalActualInteriorCodeSlice, Finset.mem_biUnion] at hleft hright
  rcases hleft with ⟨leftZ, _hleftZ, hleftCode⟩
  rcases hright with ⟨rightZ, _hrightZ, hrightCode⟩
  have hpows : 2 ^ left = 2 ^ right :=
    (globalActualInteriorCodeBand_coordinates D hleftCode).1.symm.trans
      (globalActualInteriorCodeBand_coordinates D hrightCode).1
  exact hne (Nat.pow_right_injective (by norm_num) hpows)

theorem globalActualInteriorCodeUniverse_pairwiseDisjoint (D : CarrySeries)
    (N W cap reserve : ℕ) :
    Set.PairwiseDisjoint
      (↑(Finset.range
        (Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1)))
      (globalActualInteriorCodeSlice D cap reserve) := by
  intro left _hleft right _hright hne
  exact globalActualInteriorCodeSlice_disjoint_of_ne D cap reserve hne

/-- Weight contributed by one retained word in a fixed denominator band.  The
mean-gap band and the word itself do not enter the endpoint or span caps. -/
noncomputable def globalActualInteriorHighBandWeight (D : CarrySeries)
    (W m cap F eD : ℕ) : ℕ :=
  globalActualInteriorHighEndpointCap D W m cap F
      ([], 2 ^ eD, 1) * (m + 1) *
    globalActualInteriorBlockCap D ([], 2 ^ eD, 1)

theorem globalActualInteriorHighCodeWeight_eq_bandWeight (D : CarrySeries)
    (W m cap F eD eZ : ℕ) (word : Erdos260.GapWord) :
    globalActualInteriorHighEndpointCap D W m cap F
        (word, 2 ^ eD, 2 ^ eZ) * (m + 1) *
      globalActualInteriorBlockCap D (word, 2 ^ eD, 2 ^ eZ) =
        globalActualInteriorHighBandWeight D W m cap F eD := by
  rfl

/-- Fully explicit high-frequency entropy census, indexed only by the two
dyadic exponents and the retained-word cardinality in that band. -/
noncomputable def globalActualInteriorHighEntropyCensusBound (D : CarrySeries)
    (N W m cap F reserve : ℕ) : ℕ :=
  ∑ eD ∈ Finset.range
      (Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1),
    ∑ eZ ∈ Finset.range (Nat.log 2 cap + 1),
      if reserve < 2 * 2 ^ eZ ∧ D.base ^ (2 ^ eZ) < 4 * 2 ^ eD then
        (retainedBlockWords
          (logarithmicBlockScale D.base 4 (2 ^ eD)) (2 ^ eZ)).card *
            globalActualInteriorHighBandWeight D W m cap F eD
      else 0

/-- Real high-frequency weight after replacing the endpoint ceiling by twice
its decaying real envelope.  This replacement is valid precisely on the
realized high-code image. -/
noncomputable def globalActualInteriorHighDecayCodeWeight (D : CarrySeries)
    (W m cap F : ℕ) (code : GlobalActualInteriorCode) : ℝ :=
  2 * globalActualInteriorHighEndpointEnvelope D W m cap F code *
    (m + 1) * globalActualInteriorBlockCap D code

/-- The decay weight is constant across words and mean-gap bands once the
dyadic denominator exponent is fixed. -/
noncomputable def globalActualInteriorHighDecayBandWeight (D : CarrySeries)
    (W m cap F eD : ℕ) : ℝ :=
  globalActualInteriorHighDecayCodeWeight D W m cap F ([], 2 ^ eD, 1)

theorem globalActualInteriorHighDecayCodeWeight_eq_bandWeight
    (D : CarrySeries) (W m cap F eD eZ : ℕ)
    (word : Erdos260.GapWord) :
    globalActualInteriorHighDecayCodeWeight D W m cap F
        (word, 2 ^ eD, 2 ^ eZ) =
      globalActualInteriorHighDecayBandWeight D W m cap F eD := by
  rfl

/-- Explicit real-valued entropy census with no endpoint ceiling. -/
noncomputable def globalActualInteriorHighDecayCensusBound (D : CarrySeries)
    (N W m cap F reserve : ℕ) : ℝ :=
  ∑ eD ∈ Finset.range
      (Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1),
    ∑ eZ ∈ Finset.range (Nat.log 2 cap + 1),
      if reserve < 2 * 2 ^ eZ ∧ D.base ^ (2 ^ eZ) < 4 * 2 ^ eD then
        ((retainedBlockWords
          (logarithmicBlockScale D.base 4 (2 ^ eD))
          (2 ^ eZ)).card : ℝ) *
            globalActualInteriorHighDecayBandWeight D W m cap F eD
      else 0

/-- Every denominator exponent occurring in the explicit census has block
scale at most the common window-level block scale. -/
theorem globalActualInteriorBandBlockScale_le_cap (D : CarrySeries)
    {N W cap eD : ℕ}
    (hQpos : 0 < globalActualInteriorStateDenominatorCap D N W cap)
    (heD : eD <
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1) :
    logarithmicBlockScale D.base 4 (2 ^ eD) ≤
      globalActualInteriorBlockScaleCap D N W cap := by
  have hexponent : eD ≤
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) := by
    omega
  have hband : 2 ^ eD ≤
      globalActualInteriorStateDenominatorCap D N W cap := by
    calc
      2 ^ eD ≤ 2 ^ Nat.log 2
          (globalActualInteriorStateDenominatorCap D N W cap) :=
        Nat.pow_le_pow_right (by omega) hexponent
      _ ≤ globalActualInteriorStateDenominatorCap D N W cap :=
        Nat.pow_log_le_self 2 hQpos.ne'
  unfold logarithmicBlockScale globalActualInteriorBlockScaleCap
  apply Nat.clog_mono_right
  exact Nat.mul_le_mul_left 4 hband

/-- Clearing the fixed normalization denominator costs only a fixed shift in
the dyadic exponent. -/
theorem globalActualInteriorEffectiveBandDenominator_pow_sub_le
    (D : CarrySeries)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {eD k : ℕ}
    (hfactor : D.denominator *
        (D.weight.coeff D.weight.natDegree).natAbs ≤ 2 ^ k)
    (hk : k ≤ eD) :
    2 ^ (eD - k) ≤
      globalActualInteriorEffectiveBandDenominator D ([], 2 ^ eD, 1) := by
  let C := D.denominator *
    (D.weight.coeff D.weight.natDegree).natAbs
  have hCpos : 0 < C := by
    dsimp only [C]
    exact Nat.mul_pos D.denominator_pos
      (Int.natAbs_pos.mpr (ne_of_gt hw))
  have hmul : C * 2 ^ (eD - k) ≤ 2 ^ eD := by
    calc
      C * 2 ^ (eD - k) ≤ 2 ^ k * 2 ^ (eD - k) :=
        Nat.mul_le_mul_right _ hfactor
      _ = 2 ^ eD := by
        rw [← pow_add]
        congr 1
        omega
  have hdiv : 2 ^ (eD - k) ≤ 2 ^ eD / C :=
    (Nat.le_div_iff_mul_le hCpos).2 (by simpa [mul_comm] using hmul)
  unfold globalActualInteriorEffectiveBandDenominator
  exact hdiv.trans (le_max_right _ _)

/-- Sampling power furnished by the Vandermonde fibre estimate. -/
noncomputable def globalActualInteriorSamplingExponent (D : CarrySeries) : ℝ :=
  (vandermondeExponent D.weight.natDegree : ℝ)⁻¹

/-- Entropy is absorbed using one quarter of the available sampling power. -/
noncomputable def globalActualInteriorEntropyExponent (D : CarrySeries) : ℝ :=
  globalActualInteriorSamplingExponent D / 4

/-- Geometric ratio left after entropy absorption. -/
noncomputable def globalActualInteriorDecayRatio (D : CarrySeries) : ℝ :=
  Real.rpow 2
    (globalActualInteriorEntropyExponent D -
      globalActualInteriorSamplingExponent D)

/-- Fixed dyadic exponent needed to absorb the normalization denominator. -/
def globalActualInteriorNormalizationExponent (D : CarrySeries) : ℕ :=
  Nat.clog 2
    (D.denominator * (D.weight.coeff D.weight.natDegree).natAbs)

/-- Fixed multiplicative loss caused by the normalization exponent shift. -/
noncomputable def globalActualInteriorDecayShift (D : CarrySeries) : ℝ :=
  Real.rpow 2
    (globalActualInteriorSamplingExponent D *
      globalActualInteriorNormalizationExponent D)

theorem vandermondeExponent_pos_of_degree_pos {d : ℕ} (hd : 0 < d) :
    0 < vandermondeExponent d := by
  rw [vandermondeExponent_eq]
  apply Nat.div_pos
  · nlinarith
  · norm_num

theorem globalActualInteriorSamplingExponent_pos (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) :
    0 < globalActualInteriorSamplingExponent D := by
  unfold globalActualInteriorSamplingExponent
  positivity [vandermondeExponent_pos_of_degree_pos hd]

theorem globalActualInteriorEntropyExponent_pos (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) :
    0 < globalActualInteriorEntropyExponent D := by
  unfold globalActualInteriorEntropyExponent
  positivity [globalActualInteriorSamplingExponent_pos D hd]

theorem globalActualInteriorDecayRatio_pos (D : CarrySeries) :
    0 < globalActualInteriorDecayRatio D := by
  unfold globalActualInteriorDecayRatio
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem globalActualInteriorDecayRatio_nonneg (D : CarrySeries) :
    0 ≤ globalActualInteriorDecayRatio D :=
  (globalActualInteriorDecayRatio_pos D).le

theorem globalActualInteriorDecayRatio_lt_one (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) :
    globalActualInteriorDecayRatio D < 1 := by
  unfold globalActualInteriorDecayRatio globalActualInteriorEntropyExponent
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  have hs := globalActualInteriorSamplingExponent_pos D hd
  linarith

theorem globalActualInteriorDecayShift_pos (D : CarrySeries) :
    0 < globalActualInteriorDecayShift D := by
  unfold globalActualInteriorDecayShift
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- A finite subset of a nonnegative geometric tail is bounded by the full
tail.  This local version is parameterized for the degree-dependent ratio. -/
theorem finiteGeometricTail_le (s : Finset ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hmin : ∀ i ∈ s, n ≤ i) :
    (∑ i ∈ s, r ^ i) ≤ r ^ n * (1 - r)⁻¹ := by
  have hsummable : Summable (fun i : ℕ ↦ if n ≤ i then r ^ i else 0) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).indicator
      {i : ℕ | n ≤ i}).congr ?_
    intro i
    simp [Set.indicator_apply]
  have hsumTsum :
      (∑ i ∈ s, if n ≤ i then r ^ i else 0) ≤
        ∑' i : ℕ, if n ≤ i then r ^ i else 0 :=
    hsummable.sum_le_tsum s (fun i _ ↦ by positivity)
  have htail : (∑' i : ℕ, if n ≤ i then r ^ i else 0) =
      r ^ n * (1 - r)⁻¹ := by
    have hprefix :
        (∑ i ∈ Finset.range n, if n ≤ i then r ^ i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_range] at hi
      simp [Nat.not_le.mpr hi]
    rw [← hsummable.sum_add_tsum_nat_add n, hprefix, zero_add]
    simp only [Nat.le_add_left, if_true, pow_add]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, mul_comm]
  calc
    (∑ i ∈ s, r ^ i) =
        ∑ i ∈ s, if n ≤ i then r ^ i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hmin i hi]
    _ ≤ ∑' i : ℕ, if n ≤ i then r ^ i else 0 := hsumTsum
    _ = r ^ n * (1 - r)⁻¹ := htail

theorem finiteGeometricTail_le_of_inj {A : Type*} [DecidableEq A]
    (s : Finset A) (exponent : A → ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hinj : Set.InjOn exponent s)
    (hmin : ∀ a ∈ s, n ≤ exponent a) :
    (∑ a ∈ s, r ^ exponent a) ≤ r ^ n * (1 - r)⁻¹ := by
  calc
    (∑ a ∈ s, r ^ exponent a) =
        ∑ i ∈ s.image exponent, r ^ i :=
      (Finset.sum_image hinj).symm
    _ ≤ r ^ n * (1 - r)⁻¹ := by
      apply finiteGeometricTail_le (s.image exponent) hr0 hr1 n
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      exact hmin a ha

/-- Two nested finite band sums cost two geometric-tail factors.  The outer
band may use any injective exponent map. -/
theorem finiteTwoLayerGeometricTail_le
    (sD sZ : Finset ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P]
    (weight : ℕ → ℕ → ℝ) (zExponent : ℕ → ℕ)
    (C r : ℝ) (n : ℕ)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hweight : ∀ d ∈ sD, ∀ z ∈ sZ, P d z →
      weight d z ≤ C * r ^ d)
    (hdmin : ∀ d ∈ sD, ∀ z ∈ sZ, P d z → zExponent z ≤ d)
    (hzmin : ∀ d ∈ sD, ∀ z ∈ sZ, P d z → n ≤ zExponent z)
    (hzinj : Set.InjOn zExponent sZ) :
    (∑ d ∈ sD, ∑ z ∈ sZ, if P d z then weight d z else 0) ≤
      C * (1 - r)⁻¹ * (r ^ n * (1 - r)⁻¹) := by
  classical
  let activeD : ℕ → Finset ℕ := fun z ↦ sD.filter fun d ↦ P d z
  let activeZ : Finset ℕ := sZ.filter fun z ↦ (activeD z).Nonempty
  let inner : ℕ → ℝ := fun z ↦
    ∑ d ∈ sD, if P d z then weight d z else 0
  have hinner (z : ℕ) (hz : z ∈ activeZ) :
      inner z ≤ C * (r ^ zExponent z * (1 - r)⁻¹) := by
    have hzS : z ∈ sZ := (Finset.mem_filter.mp hz).1
    have hrewrite : inner z = ∑ d ∈ activeD z, weight d z := by
      dsimp only [inner, activeD]
      rw [Finset.sum_filter]
    rw [hrewrite]
    calc
      (∑ d ∈ activeD z, weight d z) ≤
          ∑ d ∈ activeD z, C * r ^ d := by
        apply Finset.sum_le_sum
        intro d hd
        have hd' := Finset.mem_filter.mp hd
        exact hweight d hd'.1 z hzS hd'.2
      _ = C * ∑ d ∈ activeD z, r ^ d := by
        rw [Finset.mul_sum]
      _ ≤ C * (r ^ zExponent z * (1 - r)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply finiteGeometricTail_le (activeD z) hr0 hr1 (zExponent z)
        intro d hd
        have hd' := Finset.mem_filter.mp hd
        exact hdmin d hd'.1 z hzS hd'.2
  have hinactive (z : ℕ) (hzS : z ∈ sZ) (hz : z ∉ activeZ) :
      inner z = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hP : P d z
    · exfalso
      apply hz
      apply Finset.mem_filter.mpr
      exact ⟨hzS, ⟨d, Finset.mem_filter.mpr ⟨hd, hP⟩⟩⟩
    · simp [hP]
  have hrestrict : (∑ z ∈ sZ, inner z) =
      ∑ z ∈ activeZ, inner z := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hzS hzNot
    exact hinactive z hzS hzNot
  have htailNonneg : 0 ≤ (1 - r)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hr1.le)
  have houterMin : ∀ z ∈ activeZ, n ≤ zExponent z := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    obtain ⟨d, hd⟩ := hz'.2
    have hd' := Finset.mem_filter.mp hd
    exact hzmin d hd'.1 z hz'.1 hd'.2
  have houterInj : Set.InjOn zExponent activeZ :=
    hzinj.mono (Finset.filter_subset _ _)
  calc
    (∑ d ∈ sD, ∑ z ∈ sZ, if P d z then weight d z else 0) =
        ∑ z ∈ sZ, inner z := by
      dsimp only [inner]
      rw [Finset.sum_comm]
    _ = ∑ z ∈ activeZ, inner z := hrestrict
    _ ≤ ∑ z ∈ activeZ,
        C * (r ^ zExponent z * (1 - r)⁻¹) :=
      Finset.sum_le_sum hinner
    _ = (C * (1 - r)⁻¹) *
        ∑ z ∈ activeZ, r ^ zExponent z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ (C * (1 - r)⁻¹) *
        (r ^ n * (1 - r)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC htailNonneg)
      exact finiteGeometricTail_le_of_inj activeZ zExponent
        hr0 hr1 n houterInj houterMin

/-- Exponent used for the outer mean-gap sum.  Since the actual mean-gap band
is `2^eZ`, taking half still gives an injective exponent map. -/
def globalActualInteriorMeanGapTailExponent (eZ : ℕ) : ℕ :=
  2 ^ eZ / 2

theorem globalActualInteriorMeanGapTailExponent_zero :
    globalActualInteriorMeanGapTailExponent 0 = 0 := by
  norm_num [globalActualInteriorMeanGapTailExponent]

theorem globalActualInteriorMeanGapTailExponent_succ (eZ : ℕ) :
    globalActualInteriorMeanGapTailExponent (eZ + 1) = 2 ^ eZ := by
  simp [globalActualInteriorMeanGapTailExponent, pow_succ]

theorem globalActualInteriorMeanGapTailExponent_injective :
    Function.Injective globalActualInteriorMeanGapTailExponent := by
  intro left right heq
  cases left with
  | zero =>
      cases right with
      | zero => rfl
      | succ right =>
          simp only [globalActualInteriorMeanGapTailExponent_zero,
            globalActualInteriorMeanGapTailExponent_succ] at heq
          have : 0 < 2 ^ right := by positivity
          omega
  | succ left =>
      cases right with
      | zero =>
          simp only [globalActualInteriorMeanGapTailExponent_zero,
            globalActualInteriorMeanGapTailExponent_succ] at heq
          have : 0 < 2 ^ left := by positivity
          omega
      | succ right =>
          simp only [globalActualInteriorMeanGapTailExponent_succ] at heq
          have h := Nat.pow_right_injective (by norm_num : 1 < 2) heq
          omega

/-- After the fixed normalization shift, the entropy/sampling quotient is a
single geometric weight in the denominator exponent. -/
theorem globalActualInteriorDyadicRatio_le (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {eD : ℕ}
    (hk : globalActualInteriorNormalizationExponent D ≤ eD) :
    Real.rpow ((2 ^ eD : ℕ) : ℝ)
          (globalActualInteriorEntropyExponent D) /
        ((globalActualInteriorEffectiveBandDenominator
            D ([], 2 ^ eD, 1) : ℝ) ^
          globalActualInteriorSamplingExponent D) ≤
      globalActualInteriorDecayShift D *
        globalActualInteriorDecayRatio D ^ eD := by
  let k := globalActualInteriorNormalizationExponent D
  let sigma := globalActualInteriorSamplingExponent D
  let beta := globalActualInteriorEntropyExponent D
  let Deff := globalActualInteriorEffectiveBandDenominator
    D ([], 2 ^ eD, 1)
  have hfactor : D.denominator *
      (D.weight.coeff D.weight.natDegree).natAbs ≤ 2 ^ k := by
    dsimp only [k, globalActualInteriorNormalizationExponent]
    exact Nat.le_pow_clog (by omega) _
  have hDeffNat : 2 ^ (eD - k) ≤ Deff := by
    simpa only [k, Deff] using
      globalActualInteriorEffectiveBandDenominator_pow_sub_le
        D hw hfactor (by simpa only [k] using hk)
  have hDeffReal : (((2 ^ (eD - k) : ℕ) : ℝ)) ≤ Deff := by
    exact_mod_cast hDeffNat
  have hsigma : 0 < sigma := by
    simpa only [sigma] using globalActualInteriorSamplingExponent_pos D hd
  have hdenLower :
      Real.rpow (((2 ^ (eD - k) : ℕ) : ℝ)) sigma ≤
        Real.rpow (Deff : ℝ) sigma := by
    apply Real.rpow_le_rpow
    · positivity
    · exact hDeffReal
    · exact hsigma.le
  have hdenLowerPos : 0 <
      Real.rpow (((2 ^ (eD - k) : ℕ) : ℝ)) sigma := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have hrpowPow (n : ℕ) (a : ℝ) :
      Real.rpow (((2 ^ n : ℕ) : ℝ)) a =
        Real.rpow 2 ((n : ℝ) * a) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    change ((2 : ℝ) ^ n) ^ a = (2 : ℝ) ^ ((n : ℝ) * a)
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_natCast]
  have hquotient :
      Real.rpow (((2 ^ eD : ℕ) : ℝ)) beta /
          Real.rpow (Deff : ℝ) sigma ≤
        Real.rpow (((2 ^ eD : ℕ) : ℝ)) beta /
          Real.rpow (((2 ^ (eD - k) : ℕ) : ℝ)) sigma := by
    exact div_le_div_of_nonneg_left
      (Real.rpow_nonneg (by positivity) _) hdenLowerPos hdenLower
  have hexponent :
      (eD : ℝ) * beta - ((eD - k : ℕ) : ℝ) * sigma =
        sigma * k + (eD : ℝ) * (beta - sigma) := by
    rw [Nat.cast_sub (by simpa only [k] using hk)]
    ring
  calc
    Real.rpow ((2 ^ eD : ℕ) : ℝ)
          (globalActualInteriorEntropyExponent D) /
        ((Deff : ℝ) ^ globalActualInteriorSamplingExponent D) =
      Real.rpow (((2 ^ eD : ℕ) : ℝ)) beta /
        Real.rpow (Deff : ℝ) sigma := by
          rfl
    _ ≤ Real.rpow (((2 ^ eD : ℕ) : ℝ)) beta /
        Real.rpow (((2 ^ (eD - k) : ℕ) : ℝ)) sigma := hquotient
    _ = Real.rpow 2
        ((eD : ℝ) * beta - ((eD - k : ℕ) : ℝ) * sigma) := by
      rw [hrpowPow, hrpowPow]
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    _ = Real.rpow 2 (sigma * k + (eD : ℝ) * (beta - sigma)) := by
      rw [hexponent]
    _ = Real.rpow 2 (sigma * k) *
        Real.rpow 2 ((eD : ℝ) * (beta - sigma)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = Real.rpow 2 (sigma * k) *
        Real.rpow 2 ((beta - sigma) * (eD : ℝ)) := by
      rw [show (eD : ℝ) * (beta - sigma) =
          (beta - sigma) * (eD : ℝ) by ring]
    _ = Real.rpow 2 (sigma * k) *
        Real.rpow 2 (beta - sigma) ^ eD := by
      simp only [Real.rpow_eq_pow]
      rw [show (2 : ℝ) ^ ((beta - sigma) * (eD : ℝ)) =
          ((2 : ℝ) ^ (beta - sigma)) ^ eD by
        exact Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
          (beta - sigma) eD]
    _ = globalActualInteriorDecayShift D *
        globalActualInteriorDecayRatio D ^ eD := by
      rfl

/-- One coupled-band term is the window-size coefficient times the retained
word power, divided by the effective denominator sampling power. -/
theorem globalActualInteriorHighDecayBandTerm_le (D : CarrySeries)
    {N W m cap F eD eZ : ℕ} {β : ℝ}
    (hQpos : 0 < globalActualInteriorStateDenominatorCap D N W cap)
    (heD : eD <
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1)
    (hword :
      ((retainedBlockWords
          (logarithmicBlockScale D.base 4 (2 ^ eD))
          (2 ^ eZ)).card : ℝ) *
          logarithmicBlockScale D.base 4 (2 ^ eD) ≤
        Real.rpow ((2 ^ eD : ℕ) : ℝ) β) :
    ((retainedBlockWords
        (logarithmicBlockScale D.base 4 (2 ^ eD))
        (2 ^ eZ)).card : ℝ) *
        globalActualInteriorHighDecayBandWeight D W m cap F eD ≤
      16 * D.weight.natDegree *
          (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
          (m + 1) *
        (Real.rpow ((2 ^ eD : ℕ) : ℝ) β /
          (globalActualInteriorEffectiveBandDenominator
              D ([], 2 ^ eD, 1) : ℝ) ^
            ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹)) := by
  have hell := globalActualInteriorBandBlockScale_le_cap D hQpos heD
  have hinterval :
      globalActualInteriorCodeIntervalLength D W m cap F
          ([], 2 ^ eD, 1) ≤
        globalActualInteriorSampleIntervalCap D N W m cap F := by
    unfold globalActualInteriorCodeIntervalLength
      globalActualInteriorSampleIntervalCap actualInteriorSampleIntervalLength
    exact Nat.add_le_add_left hell (W + m * cap + F)
  have hdenPos : (0 : ℝ) <
      (globalActualInteriorEffectiveBandDenominator
          D ([], 2 ^ eD, 1) : ℝ) ^
        ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹) := by
    apply Real.rpow_pos_of_pos
    unfold globalActualInteriorEffectiveBandDenominator
    positivity
  have hcoef :
      (16 : ℝ) * D.weight.natDegree *
          (globalActualInteriorCodeIntervalLength D W m cap F
            ([], 2 ^ eD, 1) + 1) * (m + 1) ≤
        16 * D.weight.natDegree *
          (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
          (m + 1) := by
    gcongr
  have hnum :
      (16 : ℝ) * D.weight.natDegree *
          (globalActualInteriorCodeIntervalLength D W m cap F
            ([], 2 ^ eD, 1) + 1) * (m + 1) *
          (((retainedBlockWords
              (logarithmicBlockScale D.base 4 (2 ^ eD))
              (2 ^ eZ)).card : ℝ) *
            logarithmicBlockScale D.base 4 (2 ^ eD)) ≤
        16 * D.weight.natDegree *
          (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
          (m + 1) * Real.rpow ((2 ^ eD : ℕ) : ℝ) β :=
    mul_le_mul hcoef hword (by positivity) (by positivity)
  calc
    ((retainedBlockWords
        (logarithmicBlockScale D.base 4 (2 ^ eD))
        (2 ^ eZ)).card : ℝ) *
        globalActualInteriorHighDecayBandWeight D W m cap F eD =
      16 * D.weight.natDegree *
          (globalActualInteriorCodeIntervalLength D W m cap F
            ([], 2 ^ eD, 1) + 1) * (m + 1) *
        (((retainedBlockWords
            (logarithmicBlockScale D.base 4 (2 ^ eD))
            (2 ^ eZ)).card : ℝ) *
          logarithmicBlockScale D.base 4 (2 ^ eD)) /
        (globalActualInteriorEffectiveBandDenominator
            D ([], 2 ^ eD, 1) : ℝ) ^
          ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹) := by
      unfold globalActualInteriorHighDecayBandWeight
        globalActualInteriorHighDecayCodeWeight
        globalActualInteriorHighEndpointEnvelope
        globalActualInteriorBlockCap
      push_cast
      ring
    _ ≤ 16 * D.weight.natDegree *
          (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
          (m + 1) *
        (Real.rpow ((2 ^ eD : ℕ) : ℝ) β /
          (globalActualInteriorEffectiveBandDenominator
              D ([], 2 ^ eD, 1) : ℝ) ^
            ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹)) := by
      calc
        _ ≤ (16 * D.weight.natDegree *
              (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
              (m + 1) * Real.rpow ((2 ^ eD : ℕ) : ℝ) β) /
            ((globalActualInteriorEffectiveBandDenominator
                D ([], 2 ^ eD, 1) : ℝ) ^
              ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹)) :=
          div_le_div_of_nonneg_right hnum hdenPos.le
        _ = _ := by ring

/-- The band coupling `b^Z < 4D` implies `Z < ell_D`, so the uniform choice
`alpha = 5/Z` satisfies the exact composition-entropy hypothesis once the
reserve is at least twenty. -/
theorem retainedBlockWords_entropy_of_coupled_bands (D : CarrySeries)
    {reserve eD eZ : ℕ} (hreserveMin : 20 ≤ reserve)
    (hband : reserve < 2 * 2 ^ eZ ∧
      D.base ^ (2 ^ eZ) < 4 * 2 ^ eD) :
    let ell := logarithmicBlockScale D.base 4 (2 ^ eD)
    let Z := 2 ^ eZ
    ((retainedBlockWords ell Z).card : ℝ) ≤
      ((4 * ell + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2
          (((4 * ell + 1 : ℕ) : ℝ) *
            Erdos260.binaryEntropy (5 / (Z : ℝ))) := by
  dsimp only
  let ell := logarithmicBlockScale D.base 4 (2 ^ eD)
  let Z := 2 ^ eZ
  have hbase : 1 < D.base :=
    lt_of_lt_of_le (by decide : 1 < 2) D.base_ge_two
  have hfour : 4 * 2 ^ eD ≤ D.base ^ ell := by
    simpa only [ell, logarithmicBlockScale] using
      Nat.le_pow_clog hbase (4 * 2 ^ eD)
  have hpowLt : D.base ^ Z < D.base ^ ell := by
    exact hband.2.trans_le hfour
  have hZell : Z < ell :=
    (Nat.pow_lt_pow_iff_right hbase).mp hpowLt
  have hell : 0 < ell := (Nat.zero_le Z).trans_lt hZell
  have hZpos : 0 < Z := by dsimp only [Z]; positivity
  have hZten : 10 ≤ Z := by
    dsimp only [Z] at hband ⊢
    omega
  let α : ℝ := 5 / Z
  have hα0 : 0 < α := by dsimp only [α]; positivity
  have hαhalf : α ≤ 1 / 2 := by
    dsimp only [α]
    have hZreal : (10 : ℝ) ≤ Z := by exact_mod_cast hZten
    have hZrealPos : (0 : ℝ) < Z := by positivity
    rw [div_le_iff₀ hZrealPos]
    nlinarith
  have hratio : ((16 * ell / Z + 1 : ℕ) : ℝ) ≤
      α * (4 * ell + 1 : ℕ) := by
    have hZrealPos : (0 : ℝ) < Z := by exact_mod_cast hZpos
    have hZellReal : (Z : ℝ) ≤ ell := by exact_mod_cast hZell.le
    have hcastDiv : ((16 * ell / Z : ℕ) : ℝ) ≤
        ((16 * ell : ℕ) : ℝ) / Z := Nat.cast_div_le
    have hscaled : ((16 * ell / Z : ℕ) : ℝ) * Z ≤
        (16 : ℝ) * ell := by
      calc
        ((16 * ell / Z : ℕ) : ℝ) * Z ≤
            (((16 * ell : ℕ) : ℝ) / Z) * Z :=
          mul_le_mul_of_nonneg_right hcastDiv hZrealPos.le
        _ = (16 : ℝ) * ell := by
          push_cast
          field_simp
    dsimp only [α]
    push_cast
    rw [show (5 / (Z : ℝ)) * (4 * (ell : ℝ) + 1) =
        (5 * (4 * (ell : ℝ) + 1)) / Z by ring]
    rw [le_div_iff₀ hZrealPos]
    nlinarith
  simpa only [ell, Z, α] using
    retainedBlockWords_entropy ell Z hell α hα0 hαhalf hratio

/-- A power-parameterized version of the elementary logarithmic absorption
estimate.  It is uniform in the integer scale `D` and will let the entropy
exponent be chosen below the sampling exponent in every polynomial degree. -/
theorem eventually_logarithmic_entropy_bound_power (C β : ℝ)
    (hC : 0 < C) (hβ : 0 < β) :
    ∀ᶠ D : ℕ in atTop,
      let ell := Nat.ceil (Real.logb 2 (4 * D))
      C * (ell : ℝ) ^ 4 *
          Real.rpow 2 ((β / 2) * ell) ≤ Real.rpow D β := by
  let a : ℝ := β / 2
  let K : ℝ := C * 625 * Real.rpow 8 a
  have ha : 0 < a := by dsimp only [a]; positivity
  have hK : 0 < K := by
    dsimp only [K]
    exact mul_pos (mul_pos hC (by norm_num))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (4 : ℝ) ha).bound
      (show 0 < (1 : ℝ) / K by positivity)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 3] with D hsmall hD
  dsimp only
  have hDpos : (0 : ℝ) < D := by positivity
  have hlog : 1 ≤ Real.log (D : ℝ) := by
    rw [Real.le_log_iff_exp_le hDpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hD)
  have hlog0 : 0 ≤ Real.log (D : ℝ) := le_trans (by norm_num) hlog
  have hsmall' : Real.log (D : ℝ) ^ 4 ≤
      (1 / K) * Real.rpow D a := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 (4 : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg hDpos.le a)] at hsmall
    rw [← Real.rpow_natCast]
    exact hsmall
  have habsorb : K * Real.log (D : ℝ) ^ 4 ≤ Real.rpow D a := by
    calc
      _ ≤ K * ((1 / K) * Real.rpow D a) :=
        mul_le_mul_of_nonneg_left hsmall' hK.le
      _ = _ := by field_simp
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 :=
    lt_of_lt_of_le (by norm_num) hlog2
  have hlogbNonneg : 0 ≤ Real.logb 2 (4 * D) := by
    rw [Real.logb]
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 4 * D by omega)
    · exact hlog2pos.le
  have hceilLt := Nat.ceil_lt_add_one hlogbNonneg
  have hident : Real.logb 2 (4 * (D : ℝ)) =
      2 + Real.log (D : ℝ) / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hDpos.ne']
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    field_simp
  have hdiv : Real.log (D : ℝ) / Real.log 2 ≤
      2 * Real.log (D : ℝ) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog2)]
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hell : (ell : ℝ) ≤ 5 * Real.log (D : ℝ) := by
    rw [show (4 * D : ℝ) = 4 * (D : ℝ) by norm_num, hident] at hceilLt
    dsimp only [ell]
    rw [show (4 * D : ℝ) = 4 * (D : ℝ) by norm_num, hident]
    linarith
  have hellpow : (ell : ℝ) ^ 4 ≤
      625 * Real.log (D : ℝ) ^ 4 := by
    have hell0 : (0 : ℝ) ≤ ell := by positivity
    have hp := pow_le_pow_left₀ hell0 hell 4
    nlinarith
  have harg : a * (ell : ℝ) ≤
      a * (Real.logb 2 (4 * (D : ℝ)) + 1) := by
    apply mul_le_mul_of_nonneg_left _ ha.le
    have hc : (ell : ℝ) < Real.logb 2 (4 * (D : ℝ)) + 1 := by
      simpa only [ell, Nat.cast_ofNat, Nat.cast_mul] using hceilLt
    exact hc.le
  have hexp : Real.rpow 2 (a * (ell : ℝ)) ≤
      Real.rpow 8 a * Real.rpow D a := by
    calc
      Real.rpow 2 (a * (ell : ℝ)) ≤
          Real.rpow 2 (a * (Real.logb 2 (4 * (D : ℝ)) + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) harg
      _ = Real.rpow (8 * (D : ℝ)) a := by
        change (2 : ℝ) ^ (a * (Real.logb 2 (4 * (D : ℝ)) + 1)) = _
        rw [show a * (Real.logb 2 (4 * (D : ℝ)) + 1) =
            (Real.logb 2 (4 * (D : ℝ)) + 1) * a by ring,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
          Real.rpow_one]
        congr 1
        ring
      _ = Real.rpow 8 a * Real.rpow D a := by
        exact Real.mul_rpow (by norm_num) hDpos.le
  have hpolyMul : C * (ell : ℝ) ^ 4 ≤
      C * (625 * Real.log (D : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left hellpow hC.le
  have hfirst := mul_le_mul hpolyMul hexp
    (Real.rpow_nonneg (by norm_num) _)
    (by positivity : 0 ≤ C * (625 * Real.log (D : ℝ) ^ 4))
  calc
    C * (ell : ℝ) ^ 4 * Real.rpow 2 ((β / 2) * ell) =
        C * (ell : ℝ) ^ 4 * Real.rpow 2 (a * ell) := by rfl
    _ ≤ C * (625 * Real.log (D : ℝ) ^ 4) *
        (Real.rpow 8 a * Real.rpow D a) := hfirst
    _ = (K * Real.log (D : ℝ) ^ 4) * Real.rpow D a := by
      dsimp only [K]
      ring
    _ ≤ Real.rpow D a * Real.rpow D a :=
      mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hDpos.le _)
    _ = Real.rpow D β := by
      calc
        Real.rpow D a * Real.rpow D a = Real.rpow D (a + a) :=
          (Real.rpow_add hDpos a a).symm
        _ = Real.rpow D β := by
          congr 1
          dsimp only [a]
          ring

/-- Quantitative block entropy with an arbitrary positive target power.  This
strengthens the older square-root absorption lemma precisely enough for the
degree-dependent Vandermonde sampling exponent. -/
theorem lem_quant_entropy_power (B c C β : ℝ)
    (hB : 2 < B) (hc : 0 < c) (hC : 0 < C) (hβ : 0 < β) :
    ∃ Zstar : ℕ, ∀ Z D : ℕ,
      Zstar ≤ Z → c * (2 : ℝ) ^ Z ≤ D →
      let ell := Nat.ceil (Real.logb 2 (4 * D))
      C * (ell : ℝ) ^ 4 *
          Real.rpow 2
            ((B + 1) * ell * Erdos260.binaryEntropy (5 / (Z : ℝ))) ≤
        Real.rpow D β := by
  have harg : Tendsto (fun Z : ℕ => (5 : ℝ) / (Z : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hEntropyTendsto : Tendsto
      (fun Z : ℕ => Erdos260.binaryEntropy (5 / (Z : ℝ)))
      atTop (𝓝 0) := by
    have hzero : Erdos260.binaryEntropy 0 = 0 := by
      simp [Erdos260.binaryEntropy]
    change Tendsto (Erdos260.binaryEntropy ∘
      fun Z : ℕ => (5 : ℝ) / (Z : ℝ)) atTop (𝓝 0)
    simpa only [hzero] using
      Erdos260.binaryEntropy_continuous.tendsto 0 |>.comp harg
  have hBplus : 0 < B + 1 := by linarith
  let δ : ℝ := (β / 2) / (B + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hEntropySmall : ∀ᶠ Z : ℕ in atTop,
      Erdos260.binaryEntropy (5 / (Z : ℝ)) ≤ δ :=
    hEntropyTendsto.eventually (eventually_le_nhds hδ)
  obtain ⟨Dstar, hDstar⟩ := eventually_atTop.mp
    (eventually_logarithmic_entropy_bound_power C β hC hβ)
  have hScaleLarge : ∀ᶠ Z : ℕ in atTop,
      (Dstar : ℝ) ≤ c * (2 : ℝ) ^ Z :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hc)
      |>.eventually_ge_atTop _
  obtain ⟨Zstar, hZstar⟩ := eventually_atTop.mp
    (hEntropySmall.and hScaleLarge)
  refine ⟨Zstar, ?_⟩
  intro Z D hZ hD
  dsimp only
  have hpair := hZstar Z hZ
  have hDstarReal : (Dstar : ℝ) ≤ D := hpair.2.trans hD
  have hDstarNat : Dstar ≤ D := by exact_mod_cast hDstarReal
  have hgeneric := hDstar D hDstarNat
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hcoef : (B + 1) *
      Erdos260.binaryEntropy (5 / (Z : ℝ)) ≤ β / 2 := by
    have hm := mul_le_mul_of_nonneg_left hpair.1 hBplus.le
    calc
      _ ≤ (B + 1) * δ := hm
      _ = β / 2 := by
        dsimp only [δ]
        field_simp
  have hexponent : (B + 1) * (ell : ℝ) *
      Erdos260.binaryEntropy (5 / (Z : ℝ)) ≤ (β / 2) * ell := by
    nlinarith [mul_le_mul_of_nonneg_left hcoef hell0]
  have hrpow : Real.rpow 2
      ((B + 1) * (ell : ℝ) *
        Erdos260.binaryEntropy (5 / (Z : ℝ))) ≤
      Real.rpow 2 ((β / 2) * ell) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  calc
    C * (ell : ℝ) ^ 4 *
        Real.rpow 2 ((B + 1) * ell *
          Erdos260.binaryEntropy (5 / (Z : ℝ))) ≤
      C * (ell : ℝ) ^ 4 * Real.rpow 2 ((β / 2) * ell) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ Real.rpow D β := by simpa only [ell] using hgeneric

/-- Canonical entropy witness used in the high-frequency word cutoff. -/
noncomputable def retainedBlockWordsQuantWitness (β : ℝ) (hβ : 0 < β) : ℕ :=
  Classical.choose (lem_quant_entropy_power 4 (1 / 4) 25 β
    (by norm_num) (by norm_num) (by norm_num) hβ)

theorem retainedBlockWordsQuantWitness_spec (β : ℝ) (hβ : 0 < β) :
    ∀ Z D : ℕ,
      retainedBlockWordsQuantWitness β hβ ≤ Z →
      (1 / 4 : ℝ) * (2 : ℝ) ^ Z ≤ D →
      let ell := Nat.ceil (Real.logb 2 (4 * D))
      (25 : ℝ) * (ell : ℝ) ^ 4 *
          Real.rpow 2
            ((4 + 1) * ell * Erdos260.binaryEntropy (5 / (Z : ℝ))) ≤
        Real.rpow D β := by
  exact Classical.choose_spec (lem_quant_entropy_power 4 (1 / 4) 25 β
    (by norm_num) (by norm_num) (by norm_num) hβ)

/-- Canonical reserve depending only on the requested entropy exponent. -/
def retainedBlockWordsReserve (β : ℝ) (hβ : 0 < β) : ℕ :=
  max 20 (2 * retainedBlockWordsQuantWitness β hβ)

theorem retainedBlockWordsReserve_congr {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (h : β = γ) :
    retainedBlockWordsReserve β hβ = retainedBlockWordsReserve γ hγ := by
  subst γ
  rfl

/-- On every coupled dyadic denominator/mean-gap band, the complete retained
word census (including one block-scale factor) is bounded by an arbitrarily
small positive power of the denominator band.  This canonical form exposes a
cutoff independent of the carry numerator and support. -/
theorem retainedBlockWords_card_mul_scale_le_band_power_from_reserve
    (D : CarrySeries)
    (β : ℝ) (hβ : 0 < β) :
    ∀ reserve eD eZ : ℕ,
      retainedBlockWordsReserve β hβ ≤ reserve →
      reserve < 2 * 2 ^ eZ ∧ D.base ^ (2 ^ eZ) < 4 * 2 ^ eD →
      ((retainedBlockWords
          (logarithmicBlockScale D.base 4 (2 ^ eD))
          (2 ^ eZ)).card : ℝ) *
          logarithmicBlockScale D.base 4 (2 ^ eD) ≤
        Real.rpow ((2 ^ eD : ℕ) : ℝ) β := by
  let Zstar := retainedBlockWordsQuantWitness β hβ
  have hquant := retainedBlockWordsQuantWitness_spec β hβ
  intro reserve eD eZ hreserve hband
  let Dband : ℕ := 2 ^ eD
  let Z : ℕ := 2 ^ eZ
  let ellb : ℕ := logarithmicBlockScale D.base 4 Dband
  let ell2 : ℕ := Nat.ceil (Real.logb 2 (4 * Dband))
  have hreserveMin : 20 ≤ reserve := by
    exact (le_max_left 20 (2 * retainedBlockWordsQuantWitness β hβ)).trans
      hreserve
  have hcoupled : reserve < 2 * Z ∧ D.base ^ Z < 4 * Dband := by
    simpa only [Z, Dband] using hband
  have hZstar : Zstar ≤ Z := by
    have htwoZstar : 2 * Zstar ≤ reserve := by
      exact (le_max_right 20 (2 * retainedBlockWordsQuantWitness β hβ)).trans
        hreserve
    omega
  have htwoPowBase : 2 ^ Z ≤ D.base ^ Z :=
    Nat.pow_le_pow_left D.base_ge_two Z
  have htwoBand : 2 ^ Z < 4 * Dband :=
    htwoPowBase.trans_lt hcoupled.2
  have htwoBandReal : (2 : ℝ) ^ Z < 4 * (Dband : ℝ) := by
    exact_mod_cast htwoBand
  have hquarter : (1 / 4 : ℝ) * (2 : ℝ) ^ Z ≤ Dband := by
    nlinarith
  have hbase : 1 < D.base :=
    lt_of_lt_of_le (by decide : 1 < 2) D.base_ge_two
  have hell2Eq : ell2 = Nat.clog 2 (4 * Dband) := by
    dsimp only [ell2]
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * Dband)
  have hfourD : 4 * Dband ≤ 2 ^ ell2 := by
    rw [hell2Eq]
    exact Nat.le_pow_clog (by omega) _
  have htwoBase : 2 ^ ell2 ≤ D.base ^ ell2 :=
    Nat.pow_le_pow_left D.base_ge_two ell2
  have hellLe : ellb ≤ ell2 := by
    dsimp only [ellb, logarithmicBlockScale]
    rw [Nat.clog_le_iff_le_pow hbase]
    exact hfourD.trans htwoBase
  have hDbandPos : 0 < Dband := by dsimp only [Dband]; positivity
  have hell2Pos : 0 < ell2 := by
    rw [hell2Eq, Nat.lt_clog_iff_pow_lt (by omega)]
    simp only [pow_zero]
    omega
  have hZten : 10 ≤ Z := by omega
  let α : ℝ := 5 / Z
  have hα0 : 0 < α := by dsimp only [α]; positivity
  have hαhalf : α ≤ 1 / 2 := by
    dsimp only [α]
    have hZreal : (10 : ℝ) ≤ Z := by exact_mod_cast hZten
    have hZrealPos : (0 : ℝ) < Z := by positivity
    rw [div_le_iff₀ hZrealPos]
    nlinarith
  have hentropyEq :
      Erdos260.binaryEntropy α = Real.binEntropy α / Real.log 2 := by
    rw [Erdos260.binaryEntropy,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog, Real.logb]
    ring
  have hentropyNonneg : 0 ≤ Erdos260.binaryEntropy α := by
    rw [hentropyEq]
    exact div_nonneg
      (Real.binEntropy_nonneg hα0.le (hαhalf.trans (by norm_num)))
      (Real.log_nonneg (by norm_num))
  have hellReal : (ellb : ℝ) ≤ ell2 := by exact_mod_cast hellLe
  have hell2One : (1 : ℝ) ≤ ell2 := by exact_mod_cast hell2Pos
  have hlinear : (((4 * ellb + 1 : ℕ) : ℝ)) ≤ 5 * (ell2 : ℝ) := by
    push_cast
    nlinarith
  have hsquare : (((4 * ellb + 1 : ℕ) : ℝ)) ^ 2 ≤
      (5 * (ell2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlinear 2
  have hpolyFirst : (((4 * ellb + 1 : ℕ) : ℝ)) ^ 2 * ellb ≤
      (5 * (ell2 : ℝ)) ^ 2 * ell2 :=
    mul_le_mul hsquare hellReal (by positivity) (by positivity)
  have hcubic : (ell2 : ℝ) ^ 3 ≤ (ell2 : ℝ) ^ 4 := by
    calc
      (ell2 : ℝ) ^ 3 ≤ (ell2 : ℝ) ^ 3 * ell2 :=
        le_mul_of_one_le_right (by positivity) hell2One
      _ = (ell2 : ℝ) ^ 4 := by ring
  have hpoly : (((4 * ellb + 1 : ℕ) : ℝ)) ^ 2 * ellb ≤
      25 * (ell2 : ℝ) ^ 4 := by
    calc
      _ ≤ (5 * (ell2 : ℝ)) ^ 2 * ell2 := hpolyFirst
      _ = 25 * (ell2 : ℝ) ^ 3 := by ring
      _ ≤ 25 * (ell2 : ℝ) ^ 4 := by gcongr
  have hexponent : (((4 * ellb + 1 : ℕ) : ℝ)) *
      Erdos260.binaryEntropy α ≤
        5 * (ell2 : ℝ) * Erdos260.binaryEntropy α :=
    mul_le_mul_of_nonneg_right hlinear hentropyNonneg
  have hrpow : Real.rpow 2
      ((((4 * ellb + 1 : ℕ) : ℝ)) * Erdos260.binaryEntropy α) ≤
      Real.rpow 2
        (5 * (ell2 : ℝ) * Erdos260.binaryEntropy α) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hcard : ((retainedBlockWords ellb Z).card : ℝ) ≤
      (((4 * ellb + 1 : ℕ) : ℝ)) ^ 2 *
        Real.rpow 2
          ((((4 * ellb + 1 : ℕ) : ℝ)) *
            Erdos260.binaryEntropy α) := by
    simpa only [ellb, Z, Dband, α] using
      retainedBlockWords_entropy_of_coupled_bands D hreserveMin hband
  have hcardMul := mul_le_mul_of_nonneg_right hcard
    (show (0 : ℝ) ≤ ellb by positivity)
  have hquantApply :
      (25 : ℝ) * (ell2 : ℝ) ^ 4 *
          Real.rpow 2
            (5 * (ell2 : ℝ) * Erdos260.binaryEntropy α) ≤
        Real.rpow (Dband : ℝ) β := by
    simpa only [ell2, α, show (4 : ℝ) + 1 = 5 by norm_num] using
      hquant Z Dband hZstar hquarter
  simpa only [ellb, Z, Dband] using (calc
    ((retainedBlockWords ellb Z).card : ℝ) * ellb ≤
        ((((4 * ellb + 1 : ℕ) : ℝ)) ^ 2 *
          Real.rpow 2
            ((((4 * ellb + 1 : ℕ) : ℝ)) *
              Erdos260.binaryEntropy α)) * ellb := hcardMul
    _ = ((((4 * ellb + 1 : ℕ) : ℝ)) ^ 2 * ellb) *
        Real.rpow 2
          ((((4 * ellb + 1 : ℕ) : ℝ)) *
            Erdos260.binaryEntropy α) := by ring
    _ ≤ (25 * (ell2 : ℝ) ^ 4) *
        Real.rpow 2
          (5 * (ell2 : ℝ) * Erdos260.binaryEntropy α) :=
      mul_le_mul hpoly hrpow (Real.rpow_nonneg (by norm_num) _)
        (by positivity)
    _ ≤ Real.rpow (Dband : ℝ) β := hquantApply)

/-- Existential compatibility wrapper for the canonical word reserve. -/
theorem retainedBlockWords_card_mul_scale_le_band_power (D : CarrySeries)
    (β : ℝ) (hβ : 0 < β) :
    ∃ reserve0 : ℕ, ∀ reserve eD eZ : ℕ,
      reserve0 ≤ reserve →
      reserve < 2 * 2 ^ eZ ∧ D.base ^ (2 ^ eZ) < 4 * 2 ^ eD →
      ((retainedBlockWords
          (logarithmicBlockScale D.base 4 (2 ^ eD))
          (2 ^ eZ)).card : ℝ) *
          logarithmicBlockScale D.base 4 (2 ^ eD) ≤
        Real.rpow ((2 ^ eD : ℕ) : ℝ) β := by
  refine ⟨retainedBlockWordsReserve β hβ, ?_⟩
  exact retainedBlockWords_card_mul_scale_le_band_power_from_reserve D β hβ

/-- Canonical reserve at which the two-layer high-frequency geometric tail is
valid. -/
def globalActualInteriorHighGeometricReserve (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) : ℕ :=
  max
    (retainedBlockWordsReserve
      (globalActualInteriorEntropyExponent D)
      (globalActualInteriorEntropyExponent_pos D hd))
    (4 * (globalActualInteriorNormalizationExponent D + 1))

/-- The full two-parameter high-frequency census has a uniform geometric
tail from the canonical reserve onward. -/
theorem globalActualInteriorHighDecayCensus_le_geometricTail_from_reserve
    (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    ∀ {N W m cap F reserve : ℕ},
      0 < globalActualInteriorStateDenominatorCap D N W cap →
      globalActualInteriorHighGeometricReserve D hd ≤ reserve →
      globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve ≤
        (16 * D.weight.natDegree *
            (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
            (m + 1) * globalActualInteriorDecayShift D) *
          (1 - globalActualInteriorDecayRatio D)⁻¹ *
          (globalActualInteriorDecayRatio D ^ (reserve / 4) *
            (1 - globalActualInteriorDecayRatio D)⁻¹) := by
  let reserveWords := retainedBlockWordsReserve
    (globalActualInteriorEntropyExponent D)
    (globalActualInteriorEntropyExponent_pos D hd)
  have hwords := retainedBlockWords_card_mul_scale_le_band_power_from_reserve
    D (globalActualInteriorEntropyExponent D)
      (globalActualInteriorEntropyExponent_pos D hd)
  let k := globalActualInteriorNormalizationExponent D
  intro N W m cap F reserve hQpos hreserve
  classical
  let sD := Finset.range
    (Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1)
  let sZ := Finset.range (Nat.log 2 cap + 1)
  let P : ℕ → ℕ → Prop := fun eD eZ ↦
    reserve < 2 * 2 ^ eZ ∧ D.base ^ (2 ^ eZ) < 4 * 2 ^ eD
  let weight : ℕ → ℕ → ℝ := fun eD eZ ↦
    ((retainedBlockWords
      (logarithmicBlockScale D.base 4 (2 ^ eD)) (2 ^ eZ)).card : ℝ) *
      globalActualInteriorHighDecayBandWeight D W m cap F eD
  let C : ℝ := 16 * D.weight.natDegree *
      (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
      (m + 1) * globalActualInteriorDecayShift D
  let r := globalActualInteriorDecayRatio D
  have hreserveWords : reserveWords ≤ reserve :=
    (le_max_left _ _).trans hreserve
  have hreserveShift : 4 * (k + 1) ≤ reserve :=
    (le_max_right _ _).trans hreserve
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity [globalActualInteriorDecayShift_pos D]
  have hr0 : 0 ≤ r := by
    simpa only [r] using globalActualInteriorDecayRatio_nonneg D
  have hr1 : r < 1 := by
    simpa only [r] using globalActualInteriorDecayRatio_lt_one D hd
  have hweight : ∀ eD ∈ sD, ∀ eZ ∈ sZ, P eD eZ →
      weight eD eZ ≤ C * r ^ eD := by
    intro eD heD eZ heZ hband
    have heD' : eD <
        Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1 :=
      by simpa only [sD, Finset.mem_range] using heD
    have hword := hwords reserve eD eZ hreserveWords
      (by simpa only [P] using hband)
    have hbandTerm := globalActualInteriorHighDecayBandTerm_le
      D (N := N) (W := W) (m := m) (cap := cap) (F := F)
        (eD := eD) (eZ := eZ) hQpos heD' hword
    have hkTail : k ≤ globalActualInteriorMeanGapTailExponent eZ := by
      dsimp only [globalActualInteriorMeanGapTailExponent]
      have hreserveBand : reserve < 2 * 2 ^ eZ := hband.1
      omega
    have htailD : globalActualInteriorMeanGapTailExponent eZ ≤ eD := by
      let Z := 2 ^ eZ
      have htwoBase : 2 ^ Z ≤ D.base ^ Z :=
        Nat.pow_le_pow_left D.base_ge_two Z
      have hpow : 2 ^ Z < 2 ^ (eD + 2) := by
        calc
          2 ^ Z ≤ D.base ^ Z := htwoBase
          _ < 4 * 2 ^ eD := by simpa only [Z] using hband.2
          _ = 2 ^ (eD + 2) := by simp [pow_add, mul_comm]
      have hZ : Z < eD + 2 :=
        (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpow
      dsimp only [globalActualInteriorMeanGapTailExponent, Z]
      omega
    have hkD : globalActualInteriorNormalizationExponent D ≤ eD := by
      simpa only [k] using hkTail.trans htailD
    have hratio := globalActualInteriorDyadicRatio_le D hd hw hkD
    calc
      weight eD eZ ≤
          16 * D.weight.natDegree *
              (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
              (m + 1) *
            (Real.rpow ((2 ^ eD : ℕ) : ℝ)
                (globalActualInteriorEntropyExponent D) /
              ((globalActualInteriorEffectiveBandDenominator
                  D ([], 2 ^ eD, 1) : ℝ) ^
                globalActualInteriorSamplingExponent D)) := by
        simpa only [weight, globalActualInteriorSamplingExponent] using hbandTerm
      _ ≤ 16 * D.weight.natDegree *
              (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
              (m + 1) *
            (globalActualInteriorDecayShift D *
              globalActualInteriorDecayRatio D ^ eD) := by
        apply mul_le_mul_of_nonneg_left hratio
        positivity
      _ = C * r ^ eD := by
        dsimp only [C, r]
        ring
  have hdmin : ∀ eD ∈ sD, ∀ eZ ∈ sZ, P eD eZ →
      globalActualInteriorMeanGapTailExponent eZ ≤ eD := by
    intro eD heD eZ heZ hband
    let Z := 2 ^ eZ
    have htwoBase : 2 ^ Z ≤ D.base ^ Z :=
      Nat.pow_le_pow_left D.base_ge_two Z
    have hpow : 2 ^ Z < 2 ^ (eD + 2) := by
      calc
        2 ^ Z ≤ D.base ^ Z := htwoBase
        _ < 4 * 2 ^ eD := by simpa only [P, Z] using hband.2
        _ = 2 ^ (eD + 2) := by simp [pow_add, mul_comm]
    have hZ : Z < eD + 2 :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpow
    dsimp only [globalActualInteriorMeanGapTailExponent, Z]
    omega
  have hzmin : ∀ eD ∈ sD, ∀ eZ ∈ sZ, P eD eZ →
      reserve / 4 ≤ globalActualInteriorMeanGapTailExponent eZ := by
    intro eD heD eZ heZ hband
    dsimp only [globalActualInteriorMeanGapTailExponent]
    have hreserveBand : reserve < 2 * 2 ^ eZ := hband.1
    omega
  have htail := finiteTwoLayerGeometricTail_le
    sD sZ P weight globalActualInteriorMeanGapTailExponent
      C r (reserve / 4) hC hr0 hr1 hweight hdmin hzmin
      globalActualInteriorMeanGapTailExponent_injective.injOn
  simpa only [globalActualInteriorHighDecayCensusBound, sD, sZ, P,
    weight, C, r] using htail

/-- Existential compatibility wrapper for the canonical geometric reserve. -/
theorem globalActualInteriorHighDecayCensus_le_geometricTail
    (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    ∃ reserve0 : ℕ, ∀ {N W m cap F reserve : ℕ},
      0 < globalActualInteriorStateDenominatorCap D N W cap →
      reserve0 ≤ reserve →
      globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve ≤
        (16 * D.weight.natDegree *
            (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
            (m + 1) * globalActualInteriorDecayShift D) *
          (1 - globalActualInteriorDecayRatio D)⁻¹ *
          (globalActualInteriorDecayRatio D ^ (reserve / 4) *
            (1 - globalActualInteriorDecayRatio D)⁻¹) := by
  refine ⟨globalActualInteriorHighGeometricReserve D hd, ?_⟩
  exact globalActualInteriorHighDecayCensus_le_geometricTail_from_reserve
    D hd hw

/-- Dimensionless high-frequency error ratio after the common interval and
window multiplicity have been bounded by `2W` and `2m`. -/
noncomputable def globalActualInteriorHighTail
    (D : CarrySeries) (reserve : ℕ) : ℝ :=
  64 * D.weight.natDegree * globalActualInteriorDecayShift D *
    (1 - globalActualInteriorDecayRatio D)⁻¹ *
    (globalActualInteriorDecayRatio D ^ (reserve / 4) *
      (1 - globalActualInteriorDecayRatio D)⁻¹)

theorem globalActualInteriorHighTail_nonneg (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) (reserve : ℕ) :
    0 ≤ globalActualInteriorHighTail D reserve := by
  unfold globalActualInteriorHighTail
  have hr := globalActualInteriorDecayRatio_lt_one D hd
  have hr0 := globalActualInteriorDecayRatio_nonneg D
  have hinv : 0 ≤ (1 - globalActualInteriorDecayRatio D)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hr.le)
  have hshift := globalActualInteriorDecayShift_pos D
  positivity

theorem globalActualInteriorHighTail_tendsto_zero (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) :
    Tendsto (globalActualInteriorHighTail D) atTop (𝓝 0) := by
  have hr0 := globalActualInteriorDecayRatio_nonneg D
  have hr1 := globalActualInteriorDecayRatio_lt_one D hd
  have hdiv : Tendsto (fun reserve : ℕ ↦ reserve / 4) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hpow : Tendsto
      (fun n : ℕ ↦ globalActualInteriorDecayRatio D ^ n)
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hcomposed : Tendsto
      (fun reserve : ℕ ↦
        globalActualInteriorDecayRatio D ^ (reserve / 4))
      atTop (𝓝 0) := hpow.comp hdiv
  let K : ℝ := 64 * D.weight.natDegree *
    globalActualInteriorDecayShift D *
    (1 - globalActualInteriorDecayRatio D)⁻¹ *
    (1 - globalActualInteriorDecayRatio D)⁻¹
  have hconst : Tendsto (fun _ : ℕ ↦ K) atTop (𝓝 K) :=
    tendsto_const_nhds
  have hmul := hconst.mul hcomposed
  have hrewrite : globalActualInteriorHighTail D = fun reserve : ℕ ↦
      K * globalActualInteriorDecayRatio D ^ (reserve / 4) := by
    funext reserve
    unfold globalActualInteriorHighTail
    dsimp only [K]
    ring_nf
  rw [hrewrite]
  simpa only [mul_zero] using hmul

/-- Once the common sample interval is at most `2W` and `m` is nonzero, the
complete high-frequency census is its dimensionless tail times `mW`, from the
canonical geometric reserve onward. -/
theorem globalActualInteriorHighDecayCensus_le_tail_mul_from_reserve
    (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    ∀ {N W m cap F reserve : ℕ},
      0 < globalActualInteriorStateDenominatorCap D N W cap →
      globalActualInteriorHighGeometricReserve D hd ≤ reserve →
      globalActualInteriorSampleIntervalCap D N W m cap F + 1 ≤ 2 * W →
      m + 1 ≤ 2 * m →
      globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve ≤
        globalActualInteriorHighTail D reserve * (m * W) := by
  intro N W m cap F reserve hQpos hreserve0 hH hm
  have hraw := globalActualInteriorHighDecayCensus_le_geometricTail_from_reserve
    D hd hw (N := N) (W := W) (m := m) (cap := cap)
      (F := F) (reserve := reserve) hQpos hreserve0
  have hr := globalActualInteriorDecayRatio_lt_one D hd
  have htailNonneg : 0 ≤
      (1 - globalActualInteriorDecayRatio D)⁻¹ *
        (globalActualInteriorDecayRatio D ^ (reserve / 4) *
          (1 - globalActualInteriorDecayRatio D)⁻¹) := by
    have hinv : 0 ≤ (1 - globalActualInteriorDecayRatio D)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    have hpow : 0 ≤ globalActualInteriorDecayRatio D ^ (reserve / 4) :=
      pow_nonneg (globalActualInteriorDecayRatio_nonneg D) _
    exact mul_nonneg hinv (mul_nonneg hpow hinv)
  have hcoef :
      (16 : ℝ) * D.weight.natDegree *
          (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
          (m + 1) * globalActualInteriorDecayShift D ≤
        64 * D.weight.natDegree * W * m *
          globalActualInteriorDecayShift D := by
    have hHR :
        (globalActualInteriorSampleIntervalCap D N W m cap F + 1 : ℝ) ≤
          2 * W := by exact_mod_cast hH
    have hmR : (m + 1 : ℝ) ≤ 2 * m := by exact_mod_cast hm
    have hproduct :
        (globalActualInteriorSampleIntervalCap D N W m cap F + 1 : ℝ) *
            (m + 1) ≤ (2 * W : ℝ) * (2 * m) :=
      mul_le_mul hHR hmR (by positivity) (by positivity)
    calc
      _ = ((16 : ℝ) * D.weight.natDegree) *
          ((globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
            (m + 1)) * globalActualInteriorDecayShift D := by ring
      _ ≤ ((16 : ℝ) * D.weight.natDegree) *
          ((2 * W : ℝ) * (2 * m)) *
          globalActualInteriorDecayShift D := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hproduct (by positivity))
          (globalActualInteriorDecayShift_pos D).le
      _ = (16 : ℝ) * D.weight.natDegree *
          ((2 * W : ℝ) * (2 * m)) *
          globalActualInteriorDecayShift D := by ring
      _ = _ := by ring
  calc
    globalActualInteriorHighDecayCensusBound D N W m cap F reserve ≤
        (16 * D.weight.natDegree *
            (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
            (m + 1) * globalActualInteriorDecayShift D) *
          (1 - globalActualInteriorDecayRatio D)⁻¹ *
          (globalActualInteriorDecayRatio D ^ (reserve / 4) *
            (1 - globalActualInteriorDecayRatio D)⁻¹) := hraw
    _ ≤ (64 * D.weight.natDegree * W * m *
          globalActualInteriorDecayShift D) *
        ((1 - globalActualInteriorDecayRatio D)⁻¹ *
          (globalActualInteriorDecayRatio D ^ (reserve / 4) *
            (1 - globalActualInteriorDecayRatio D)⁻¹)) := by
      calc
        _ = (16 * D.weight.natDegree *
              (globalActualInteriorSampleIntervalCap D N W m cap F + 1) *
              (m + 1) * globalActualInteriorDecayShift D) *
            ((1 - globalActualInteriorDecayRatio D)⁻¹ *
              (globalActualInteriorDecayRatio D ^ (reserve / 4) *
                (1 - globalActualInteriorDecayRatio D)⁻¹)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef htailNonneg
    _ = globalActualInteriorHighTail D reserve * (m * W) := by
      unfold globalActualInteriorHighTail
      ring

/-- Existential compatibility wrapper for the canonical tail-multiplication
reserve. -/
theorem globalActualInteriorHighDecayCensus_le_tail_mul (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    ∃ reserve0 : ℕ, ∀ {N W m cap F reserve : ℕ},
      0 < globalActualInteriorStateDenominatorCap D N W cap →
      reserve0 ≤ reserve →
      globalActualInteriorSampleIntervalCap D N W m cap F + 1 ≤ 2 * W →
      m + 1 ≤ 2 * m →
      globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve ≤
        globalActualInteriorHighTail D reserve * (m * W) := by
  refine ⟨globalActualInteriorHighGeometricReserve D hd, ?_⟩
  intro N W m cap F reserve hQpos hreserve hH hm
  exact globalActualInteriorHighDecayCensus_le_tail_mul_from_reserve
    D hd hw hQpos hreserve hH hm

/-- Uniform `o(mW)` form: the reserve cutoff is chosen before the window and
all dyadic ranges. -/
theorem globalActualInteriorHighDecayCensus_uniform_small (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ reserve0 : ℕ, ∀ {N W m cap F reserve : ℕ},
      reserve0 ≤ reserve →
      0 < globalActualInteriorStateDenominatorCap D N W cap →
      globalActualInteriorSampleIntervalCap D N W m cap F + 1 ≤ 2 * W →
      m + 1 ≤ 2 * m →
      globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve ≤ ε * (m * W) := by
  obtain ⟨reserveGeom, hgeom⟩ :=
    globalActualInteriorHighDecayCensus_le_tail_mul D hd hw
  have hevent : ∀ᶠ reserve : ℕ in atTop,
      globalActualInteriorHighTail D reserve ≤ ε :=
    (globalActualInteriorHighTail_tendsto_zero D hd).eventually
      (eventually_le_nhds hε)
  obtain ⟨reserveTail, htail⟩ := eventually_atTop.mp hevent
  refine ⟨max reserveGeom reserveTail, ?_⟩
  intro N W m cap F reserve hreserve hQpos hH hm
  have hgeomBound := hgeom hQpos ((le_max_left _ _).trans hreserve) hH hm
  have htailBound := htail reserve ((le_max_right _ _).trans hreserve)
  exact hgeomBound.trans
    (mul_le_mul_of_nonneg_right htailBound (by positivity))

/-- Canonical eventual threshold for the dimensionless high-frequency tail. -/
noncomputable def globalActualInteriorHighTailReserve (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) (ε : ℝ) (hε : 0 < ε) : ℕ :=
  Classical.choose <| eventually_atTop.mp <|
    (globalActualInteriorHighTail_tendsto_zero D hd).eventually
      (eventually_le_nhds hε)

theorem globalActualInteriorHighTailReserve_spec (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∀ reserve : ℕ,
      globalActualInteriorHighTailReserve D hd ε hε ≤ reserve →
      globalActualInteriorHighTail D reserve ≤ ε := by
  exact Classical.choose_spec <| eventually_atTop.mp <|
    (globalActualInteriorHighTail_tendsto_zero D hd).eventually
      (eventually_le_nhds hε)

/-- Canonical reserve for the complete `ε * mW` high-frequency estimate. -/
noncomputable def globalActualInteriorHighSmallReserve (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) (ε : ℝ) (hε : 0 < ε) : ℕ :=
  max (globalActualInteriorHighGeometricReserve D hd)
    (globalActualInteriorHighTailReserve D hd ε hε)

theorem globalActualInteriorHighDecayCensus_uniform_small_from_reserve
    (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ {N W m cap F reserve : ℕ},
      globalActualInteriorHighSmallReserve D hd ε hε ≤ reserve →
      0 < globalActualInteriorStateDenominatorCap D N W cap →
      globalActualInteriorSampleIntervalCap D N W m cap F + 1 ≤ 2 * W →
      m + 1 ≤ 2 * m →
      globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve ≤ ε * (m * W) := by
  intro N W m cap F reserve hreserve hQpos hH hm
  have hgeom := globalActualInteriorHighDecayCensus_le_tail_mul_from_reserve
    D hd hw hQpos ((le_max_left _ _).trans hreserve) hH hm
  have htail := globalActualInteriorHighTailReserve_spec D hd ε hε
    reserve ((le_max_right _ _).trans hreserve)
  exact hgeom.trans
    (mul_le_mul_of_nonneg_right htail (by positivity))

/-- The sum over the code universe is exactly the exponent-indexed entropy
census.  Pairwise disjointness of dyadic bands prevents hidden multiplicity. -/
theorem globalActualInteriorHighUniverse_sum_eq_entropyCensus (D : CarrySeries)
    (N W m cap F reserve : ℕ) :
    (∑ code ∈ globalActualInteriorCodeUniverse D N W cap reserve,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code) =
      globalActualInteriorHighEntropyCensusBound D N W m cap F reserve := by
  classical
  rw [globalActualInteriorCodeUniverse,
    Finset.sum_biUnion
      (globalActualInteriorCodeUniverse_pairwiseDisjoint D N W cap reserve)]
  unfold globalActualInteriorHighEntropyCensusBound
  apply Finset.sum_congr rfl
  intro eD heD
  rw [globalActualInteriorCodeSlice,
    Finset.sum_biUnion
      (globalActualInteriorCodeSlice_pairwiseDisjoint D cap reserve eD)]
  apply Finset.sum_congr rfl
  intro eZ heZ
  by_cases hband : reserve < 2 * 2 ^ eZ ∧
      D.base ^ (2 ^ eZ) < 4 * 2 ^ eD
  · rw [globalActualInteriorCodeBand, if_pos hband, if_pos hband]
    rw [Finset.sum_image]
    · simp only [globalActualInteriorHighCodeWeight_eq_bandWeight,
        Finset.sum_const_nat]
    · intro left _hleft right _hright heq
      exact congrArg Prod.fst heq
  · simp [globalActualInteriorCodeBand, hband]

/-- The corresponding real decay weight sums exactly to the real-valued
exponent census. -/
theorem globalActualInteriorHighUniverse_decay_sum_eq_census
    (D : CarrySeries) (N W m cap F reserve : ℕ) :
    (∑ code ∈ globalActualInteriorCodeUniverse D N W cap reserve,
        globalActualInteriorHighDecayCodeWeight D W m cap F code) =
      globalActualInteriorHighDecayCensusBound
        D N W m cap F reserve := by
  classical
  rw [globalActualInteriorCodeUniverse,
    Finset.sum_biUnion
      (globalActualInteriorCodeUniverse_pairwiseDisjoint D N W cap reserve)]
  unfold globalActualInteriorHighDecayCensusBound
  apply Finset.sum_congr rfl
  intro eD heD
  rw [globalActualInteriorCodeSlice,
    Finset.sum_biUnion
      (globalActualInteriorCodeSlice_pairwiseDisjoint D cap reserve eD)]
  apply Finset.sum_congr rfl
  intro eZ heZ
  by_cases hband : reserve < 2 * 2 ^ eZ ∧
      D.base ^ (2 ^ eZ) < 4 * 2 ^ eD
  · rw [globalActualInteriorCodeBand, if_pos hband, if_pos hband]
    rw [Finset.sum_image]
    · simp only [globalActualInteriorHighDecayCodeWeight_eq_bandWeight,
        Finset.sum_const, nsmul_eq_mul]
    · intro left _hleft right _hright heq
      exact congrArg Prod.fst heq
  · simp [globalActualInteriorCodeBand, hband]

/-- Every genuine retained source at the canonical threshold lands in the
explicit exponent-indexed code universe. -/
theorem globalActualInteriorCode_mem_universe (D : CarrySeries)
    {N W m cap reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (source : GlobalActualInteriorBlockSource D hgeom hW hscale
      hpositiveFrom (globalActualInteriorThreshold D N W m cap reserve)) :
    globalActualInteriorCode D source ∈
      globalActualInteriorCodeUniverse D N W cap reserve := by
  classical
  let eD := globalActualInteriorDenominatorExponent D source
  let eZ := globalActualInteriorMeanGapExponent D source
  have heD : eD <
      Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) + 1 := by
    exact Nat.lt_succ_iff.mpr
      (globalActualInteriorDenominatorExponent_le D hw source)
  have heZ : eZ < Nat.log 2 cap + 1 := by
    exact Nat.lt_succ_iff.mpr (globalActualInteriorMeanGapExponent_le D source)
  have hreserve : reserve < 2 * 2 ^ eZ := by
    simpa only [eZ, ← globalActualInteriorMeanGapBand_eq_pow_exponent] using
      globalActualInteriorReserve_lt_two_mul_meanGapBand D hw source
  have hcouple : D.base ^ (2 ^ eZ) < 4 * 2 ^ eD := by
    have hZeq : 2 ^ eZ = globalActualInteriorMeanGapBand D source := by
      simpa only [eZ] using
        (globalActualInteriorMeanGapBand_eq_pow_exponent D source).symm
    have hDeq : globalActualInteriorDenominatorBand D source = 2 ^ eD := by
      simpa only [eD] using
        globalActualInteriorDenominatorBand_eq_pow_exponent D source
    rw [hZeq, ← hDeq]
    exact globalActualInteriorMeanGapBand_base_pow_lt_four_mul_denominatorBand
      D hw source
  rw [globalActualInteriorCodeUniverse]
  refine Finset.mem_biUnion.mpr ⟨eD, Finset.mem_range.mpr heD, ?_⟩
  rw [globalActualInteriorCodeSlice]
  refine Finset.mem_biUnion.mpr ⟨eZ, Finset.mem_range.mpr heZ, ?_⟩
  rw [globalActualInteriorCodeBand, if_pos ⟨hreserve, hcouple⟩,
    Finset.mem_image]
  refine ⟨globalActualInteriorBlockWord D source, ?_, ?_⟩
  · have hword := canonicalActualInteriorBlockWord_mem_retainedWords
      D hw hgeom
        (globalActualInteriorThreshold_covers
          D hgeom hW hscale hpositiveFrom hw reserve source.1) source.2
    simpa only [globalActualInteriorBlockWord, actualInteriorBlockScale,
      globalActualInteriorDenominatorBand,
      globalActualInteriorDenominatorExponent, eD,
      globalActualInteriorMeanGapBand,
      globalActualInteriorMeanGapExponent, actualInteriorMeanGapBand,
      meanGapBand, eZ, dyadicFloorBand] using hword
  · unfold globalActualInteriorCode
    rw [globalActualInteriorDenominatorBand_eq_pow_exponent,
      globalActualInteriorMeanGapBand_eq_pow_exponent]

/-- Hence every code realized by a deep graph key is contained in the common
finite universe. -/
theorem globalActualInteriorCodeKeys_subset_universe (D : CarrySeries)
    {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    let graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    interiorCensusHighCodeKeys sources graphOf Prod.snd endpoint U ⊆
      globalActualInteriorCodeUniverse D N W cap reserve := by
  classical
  dsimp only
  intro code hcode
  rcases Finset.mem_image.mp hcode with ⟨graph, hgraph, hcodeEq⟩
  have hgraph' := (Finset.mem_filter.mp hgraph).1
  rcases Finset.mem_image.mp hgraph' with ⟨source, hsource, hgraphEq⟩
  have hmem := globalActualInteriorCode_mem_universe D hw source
  have : code = globalActualInteriorCode D source := by
    calc
      code = graph.2 := hcodeEq.symm
      _ = (globalActualInteriorGraphKey D source).2 :=
        congrArg Prod.snd hgraphEq.symm
      _ = globalActualInteriorCode D source := rfl
  simpa only [this] using hmem

/-- On a code that is genuinely represented by a high-frequency graph, the
natural ceiling in the endpoint cap costs at most a factor two.  This is the
reason for retaining the exact high-code image in `prop_interior`: the
frequency lower bound forces the real endpoint envelope above one. -/
theorem globalActualInteriorHighCode_cap_cast_le_two_envelope
    (D : CarrySeries) {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    {code : GlobalActualInteriorCode}
    (hcode :
      let threshold := globalActualInteriorThreshold D N W m cap reserve
      let sources := globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom) threshold F
      let graphOf := globalActualInteriorGraphKey D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom)
      let endpoint := globalActualInteriorEndpoint D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom)
      code ∈ interiorCensusHighCodeKeys
        sources graphOf Prod.snd endpoint U) :
    (globalActualInteriorHighEndpointCap D W m cap F code : ℝ) ≤
      2 * globalActualInteriorHighEndpointEnvelope D W m cap F code := by
  classical
  dsimp only at hcode
  rcases Finset.mem_image.mp hcode with ⟨graph, hgraph, hcodeEq⟩
  have hgraphData := Finset.mem_filter.mp hgraph
  rcases Finset.mem_image.mp hgraphData.1 with
    ⟨source, hsource, hgraphEq⟩
  have hdeep : source.Deep D F := (Finset.mem_filter.mp hsource).2
  have hshort := globalActualInterior_short_separation
    D hw
      (fun pfx ↦ globalActualInteriorThreshold_covers
        D hgeom hW hscale hpositiveFrom hw reserve pfx)
      source
  have hhigh : U ≤ (interiorCensusEndpointFibre
      (globalActualInteriorDeepSources D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom)
        (globalActualInteriorThreshold D N W m cap reserve) F)
      (globalActualInteriorGraphKey D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorEndpoint D
        (hgeom := hgeom) (hW := hW) (hscale := hscale)
        (hpositiveFrom := hpositiveFrom))
      (globalActualInteriorGraphKey D source)).card := by
    simpa only [InteriorCensusHigh, hgraphEq] using hgraphData.2
  have hcap := globalActualInteriorEndpointFibre_card_le_high_cap_total
    D hd hw
      (fun pfx ↦ globalActualInteriorThreshold_covers
        D hgeom hW hscale hpositiveFrom hw reserve pfx)
      hU source hdeep hshort hhigh
  have hsourceCode : code = globalActualInteriorCode D source := by
    calc
      code = graph.2 := hcodeEq.symm
      _ = (globalActualInteriorGraphKey D source).2 :=
        congrArg Prod.snd hgraphEq.symm
      _ = globalActualInteriorCode D source := rfl
  rw [hsourceCode]
  let envelope := globalActualInteriorHighEndpointEnvelope
    D W m cap F (globalActualInteriorCode D source)
  have hUcap : U ≤ globalActualInteriorHighEndpointCap
      D W m cap F (globalActualInteriorCode D source) := hhigh.trans hcap
  have hthree : 3 ≤ globalActualInteriorHighEndpointCap
      D W m cap F (globalActualInteriorCode D source) := by omega
  have henvNonneg : 0 ≤ envelope := by
    dsimp only [envelope, globalActualInteriorHighEndpointEnvelope,
      globalActualInteriorEffectiveBandDenominator]
    positivity
  have hceilLt :
      (globalActualInteriorHighEndpointCap
          D W m cap F (globalActualInteriorCode D source) : ℝ) <
        envelope + 1 := by
    simpa only [globalActualInteriorHighEndpointCap, envelope] using
      Nat.ceil_lt_add_one henvNonneg
  have hthreeReal : (3 : ℝ) ≤
      globalActualInteriorHighEndpointCap
        D W m cap F (globalActualInteriorCode D source) := by
    exact_mod_cast hthree
  have henvOne : 1 ≤ envelope := by linarith
  have hfinal :
      (globalActualInteriorHighEndpointCap
          D W m cap F (globalActualInteriorCode D source) : ℝ) ≤
        2 * envelope :=
    le_of_lt (hceilLt.trans_le (by nlinarith))
  simpa only [envelope] using hfinal

/-- The complete realized high-frequency mass, after casting to `ℝ`, is
bounded by the ceiling-free dyadic entropy census. -/
theorem globalActualInteriorHighMass_cast_le_decayCensus
    (D : CarrySeries) {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    let graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    ((∑ code ∈ interiorCensusHighCodeKeys
        sources graphOf Prod.snd endpoint U,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code : ℕ) : ℝ) ≤
      globalActualInteriorHighDecayCensusBound
        D N W m cap F reserve := by
  classical
  dsimp only
  let highCodes := interiorCensusHighCodeKeys
    (globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
      (globalActualInteriorThreshold D N W m cap reserve) F)
    (globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)) Prod.snd
    (globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)) U
  let codeUniverse := globalActualInteriorCodeUniverse D N W cap reserve
  have hterm : ∀ code ∈ highCodes,
      (globalActualInteriorHighEndpointCap D W m cap F code : ℝ) *
          (m + 1) * globalActualInteriorBlockCap D code ≤
        globalActualInteriorHighDecayCodeWeight D W m cap F code := by
    intro code hcode
    have hcap := globalActualInteriorHighCode_cap_cast_le_two_envelope
      D hd hw hU (code := code) (by simpa only [highCodes] using hcode)
    unfold globalActualInteriorHighDecayCodeWeight
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcap (by positivity)) (by positivity)
  have hsubset : highCodes ⊆ codeUniverse := by
    simpa only [highCodes, codeUniverse] using
      (globalActualInteriorCodeKeys_subset_universe
        D (U := U) hw)
  have hweightNonneg : ∀ code,
      0 ≤ globalActualInteriorHighDecayCodeWeight D W m cap F code := by
    intro code
    unfold globalActualInteriorHighDecayCodeWeight
      globalActualInteriorHighEndpointEnvelope
      globalActualInteriorEffectiveBandDenominator
    positivity
  have hdiffNonneg : 0 ≤
      ∑ code ∈ codeUniverse \ highCodes,
        globalActualInteriorHighDecayCodeWeight D W m cap F code :=
    Finset.sum_nonneg fun code _ ↦ hweightNonneg code
  calc
    ((∑ code ∈ highCodes,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code : ℕ) : ℝ) =
        ∑ code ∈ highCodes,
          (globalActualInteriorHighEndpointCap D W m cap F code : ℝ) *
            (m + 1) * globalActualInteriorBlockCap D code := by push_cast; rfl
    _ ≤ ∑ code ∈ highCodes,
        globalActualInteriorHighDecayCodeWeight D W m cap F code := by
      exact Finset.sum_le_sum hterm
    _ ≤ ∑ code ∈ codeUniverse,
        globalActualInteriorHighDecayCodeWeight D W m cap F code := by
      calc
        _ ≤ (∑ code ∈ codeUniverse \ highCodes,
              globalActualInteriorHighDecayCodeWeight D W m cap F code) +
            ∑ code ∈ highCodes,
              globalActualInteriorHighDecayCodeWeight D W m cap F code :=
          le_add_of_nonneg_left hdiffNonneg
        _ = _ := Finset.sum_sdiff hsubset
    _ = globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve := by
      simpa only [codeUniverse] using
        globalActualInteriorHighUniverse_decay_sum_eq_census
          D N W m cap F reserve

/-- The complete low-frequency contribution has the explicit cell-count
bound used in the manuscript.  In particular no entropy or coalescence input
is needed in this branch. -/
theorem globalActualInteriorLowMass_le (D : CarrySeries)
    {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    let graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    (∑ graph ∈ interiorCensusGraphKeys sources graphOf,
        if ¬ InteriorCensusHigh sources graphOf endpoint U graph then
          U * (m + 1) * globalActualInteriorBlockCap D graph.2
        else 0) ≤
      ((canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card *
          (m + 1) * (Nat.log 2 cap + 1)) *
        (U * (m + 1) *
          (4 * globalActualInteriorBlockScaleCap D N W cap)) := by
  classical
  dsimp only
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let sources := globalActualInteriorDeepSources D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) threshold F
  let graphOf := globalActualInteriorGraphKey D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) (threshold := threshold)
  let endpoint := globalActualInteriorEndpoint D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) (threshold := threshold)
  let graphs := interiorCensusGraphKeys sources graphOf
  let M := U * (m + 1) *
    (4 * globalActualInteriorBlockScaleCap D N W cap)
  have hterm : ∀ graph ∈ graphs,
      (if ¬ InteriorCensusHigh sources graphOf endpoint U graph then
          U * (m + 1) * globalActualInteriorBlockCap D graph.2
        else 0) ≤ M := by
    intro graph hgraph
    by_cases hhigh : InteriorCensusHigh sources graphOf endpoint U graph
    · simp [hhigh, M]
    · simp only [hhigh, not_false_eq_true, if_true]
      rcases Finset.mem_image.mp hgraph with ⟨source, hsource, hgraphEq⟩
      have hcap := globalActualInteriorBlockCap_le_uniform D hw source
      have hcode : graph.2 = globalActualInteriorCode D source := by
        simpa only [graphOf, globalActualInteriorGraphKey] using
          congrArg Prod.snd hgraphEq.symm
      rw [hcode]
      exact Nat.mul_le_mul_left (U * (m + 1)) hcap
  calc
    ∑ graph ∈ graphs,
        (if ¬ InteriorCensusHigh sources graphOf endpoint U graph then
            U * (m + 1) * globalActualInteriorBlockCap D graph.2
          else 0) ≤ ∑ _graph ∈ graphs, M := by
      exact Finset.sum_le_sum hterm
    _ = graphs.card * M := by simp
    _ ≤ ((canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card *
          (m + 1) * (Nat.log 2 cap + 1)) * M := by
      apply Nat.mul_le_mul_right
      exact globalActualInteriorGraphKeys_card_le D
        (fun pfx => globalActualInteriorThreshold_covers
          D hgeom hW hscale hpositiveFrom hw reserve pfx)
    _ = _ := rfl

/-- The high-frequency census sum can be enlarged to the explicit dyadic code
universe.  This is the exact point where realized graph data disappear from
the remaining entropy estimate. -/
theorem globalActualInteriorHighMass_le_universe (D : CarrySeries)
    {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    let graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    (∑ code ∈ interiorCensusHighCodeKeys
        sources graphOf Prod.snd endpoint U,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code) ≤
      ∑ code ∈ globalActualInteriorCodeUniverse D N W cap reserve,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code := by
  classical
  dsimp only
  exact Finset.sum_le_sum_of_subset
    (globalActualInteriorCodeKeys_subset_universe D hw)

/-- Realized high-frequency mass is bounded by the explicit exponent-indexed
entropy census. -/
theorem globalActualInteriorHighMass_le_entropyCensus (D : CarrySeries)
    {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hw : 0 < D.weight.coeff D.weight.natDegree) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    let graphOf := globalActualInteriorGraphKey D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    let endpoint := globalActualInteriorEndpoint D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom)
    (∑ code ∈ interiorCensusHighCodeKeys
        sources graphOf Prod.snd endpoint U,
        globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
          globalActualInteriorBlockCap D code) ≤
      globalActualInteriorHighEntropyCensusBound D N W m cap F reserve := by
  classical
  dsimp only
  exact (globalActualInteriorHighMass_le_universe D hw).trans_eq
    (globalActualInteriorHighUniverse_sum_eq_entropyCensus
      D N W m cap F reserve)

/-- Closed finite bound for the deep retained interior mass.  Its right-hand
side now contains only window-level parameters and the explicit entropy
census; all graph, endpoint, and source fibres have been discharged. -/
theorem globalActualInteriorDeepMass_le_finiteBound (D : CarrySeries)
    {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : globalActualInteriorUniformCoalescenceEnvelope
      D N W m cap U F < (D.base : ℝ) ^ F) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    (∑ source ∈ sources, globalActualInteriorBlockSpan D source) ≤
      ((canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card *
          (m + 1) * (Nat.log 2 cap + 1)) *
        (U * (m + 1) *
          (4 * globalActualInteriorBlockScaleCap D N W cap)) +
      globalActualInteriorHighEntropyCensusBound D N W m cap F reserve := by
  classical
  dsimp only
  have hfinite := globalActual_prop_interior_of_uniform_envelope
    D (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) hd hw reserve hU hF henvelope
  exact hfinite.trans (Nat.add_le_add
    (globalActualInteriorLowMass_le D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) hw)
    (globalActualInteriorHighMass_le_entropyCensus D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) hw))

/-- Window-level low-frequency census bound, separated out so that the
real-valued high-frequency decay estimate can be assembled without carrying
any realized graph or source family in its final interface. -/
def globalActualInteriorLowCensusBound (D : CarrySeries)
    (N W m cap U : ℕ) : ℕ :=
  ((canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card *
      (m + 1) * (Nat.log 2 cap + 1)) *
    (U * (m + 1) *
      (4 * globalActualInteriorBlockScaleCap D N W cap))

/-- Real-valued deep-mass bound with the genuine high-frequency decay
census.  This is the form needed for a uniform `o(mW)` conclusion. -/
theorem globalActualInteriorDeepMass_cast_le_decayBound (D : CarrySeries)
    {N W m cap F U reserve : ℕ}
    {hgeom : WindowGeometry D.positiveEnumeration N W m cap}
    {hW : W ≤ N} {hscale : lockingThreshold D N + cap ≤ N}
    {hpositiveFrom : D.positiveFrom ≤ N}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : globalActualInteriorUniformCoalescenceEnvelope
      D N W m cap U F < (D.base : ℝ) ^ F) :
    let threshold := globalActualInteriorThreshold D N W m cap reserve
    let sources := globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F
    ((∑ source ∈ sources,
        globalActualInteriorBlockSpan D source : ℕ) : ℝ) ≤
      (globalActualInteriorLowCensusBound D N W m cap U : ℝ) +
        globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve := by
  classical
  dsimp only
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let sources := globalActualInteriorDeepSources D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) threshold F
  let graphOf := globalActualInteriorGraphKey D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) (threshold := threshold)
  let endpoint := globalActualInteriorEndpoint D
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) (threshold := threshold)
  let lowMass : ℕ :=
    ∑ graph ∈ interiorCensusGraphKeys sources graphOf,
      if ¬ InteriorCensusHigh sources graphOf endpoint U graph then
        U * (m + 1) * globalActualInteriorBlockCap D graph.2
      else 0
  let highMass : ℕ :=
    ∑ code ∈ interiorCensusHighCodeKeys
        sources graphOf Prod.snd endpoint U,
      globalActualInteriorHighEndpointCap D W m cap F code * (m + 1) *
        globalActualInteriorBlockCap D code
  have hfinite := globalActual_prop_interior_of_uniform_envelope
    D (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) hd hw reserve hU hF henvelope
  dsimp only at hfinite
  change (∑ source ∈ sources,
      globalActualInteriorBlockSpan D source) ≤ lowMass + highMass at hfinite
  have hlow := globalActualInteriorLowMass_le D
    (F := F) (U := U) (reserve := reserve)
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) hw
  dsimp only at hlow
  change lowMass ≤ globalActualInteriorLowCensusBound D N W m cap U at hlow
  have hhigh := globalActualInteriorHighMass_cast_le_decayCensus
    D (F := F) (U := U) (reserve := reserve)
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) hd hw hU
  dsimp only at hhigh
  change (highMass : ℝ) ≤
    globalActualInteriorHighDecayCensusBound D N W m cap F reserve at hhigh
  have hfiniteReal :
      ((∑ source ∈ sources,
        globalActualInteriorBlockSpan D source : ℕ) : ℝ) ≤
        (lowMass : ℝ) + (highMass : ℝ) := by
    exact_mod_cast hfinite
  have hlowReal : (lowMass : ℝ) ≤
      globalActualInteriorLowCensusBound D N W m cap U := by
    exact_mod_cast hlow
  exact hfiniteReal.trans (add_le_add hlowReal hhigh)

/-- The full globally eligible interior mass is bounded by its explicit
low-frequency census, the uniformly decaying high-frequency census, and one
terminal suffix charge per original window index. -/
theorem globalActualInteriorEligibleStabilizedMass_cast_le_decay_add_terminal
    (D : CarrySeries) {N W m cap reserve F U : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : globalActualInteriorUniformCoalescenceEnvelope
      D N W m cap U F < (D.base : ℝ) ^ F) :
    (globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom
        (globalActualInteriorThreshold D N W m cap reserve) : ℝ) ≤
      4 * ((globalActualInteriorLowCensusBound D N W m cap U : ℝ) +
        globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve) +
      4 * enumeratedWindowCount D.positiveEnumeration N W *
        (F + 4 * globalActualInteriorBlockScaleCap D N W cap) := by
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let deepMass : ℕ := ∑ source ∈ globalActualInteriorDeepSources D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) threshold F,
    globalActualInteriorBlockSpan D
      (hgeom := hgeom) (hW := hW) (hscale := hscale)
      (hpositiveFrom := hpositiveFrom) source
  have hcover :=
    globalActualInteriorEligibleStabilizedMass_le_deep_add_terminal
      D hgeom hW hscale hpositiveFrom hw (reserve := reserve) (F := F)
  change globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
      hpositiveFrom threshold ≤
    4 * deepMass +
      4 * enumeratedWindowCount D.positiveEnumeration N W *
        (F + 4 * globalActualInteriorBlockScaleCap D N W cap) at hcover
  have hcoverReal :
      (globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
          hpositiveFrom threshold : ℝ) ≤
        4 * (deepMass : ℝ) +
          4 * enumeratedWindowCount D.positiveEnumeration N W *
            (F + 4 * globalActualInteriorBlockScaleCap D N W cap) := by
    exact_mod_cast hcover
  have hdeep := globalActualInteriorDeepMass_cast_le_decayBound
    D (F := F) (U := U) (reserve := reserve)
    (hgeom := hgeom) (hW := hW) (hscale := hscale)
    (hpositiveFrom := hpositiveFrom) hd hw hU hF henvelope
  dsimp only at hdeep
  change (deepMass : ℝ) ≤
      (globalActualInteriorLowCensusBound D N W m cap U : ℝ) +
        globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve at hdeep
  exact hcoverReal.trans (add_le_add
    (mul_le_mul_of_nonneg_left hdeep (by positivity)) (le_refl _))

/-! ## Four-class finite master inequality -/

def globalActualShortMassBound (D : CarrySeries)
    (N W m cap reserve : ℕ) : ℕ :=
  globalActualClassificationCutoff D N W m cap reserve *
    enumeratedWindowCount D.positiveEnumeration N W

def globalActualRareMassBound (D : CarrySeries)
    (N W m cap : ℕ) : ℕ :=
  (globalActualRarePrefixes D N W m).card *
    (D.weight.natDegree + 1) * (m * cap)

/-- Complete real-valued interior contribution after the global cover: low
census, decaying high census, shallow terminal loss, and deterministic
classification/absorption loss. -/
noncomputable def globalActualInteriorAssembledBound (D : CarrySeries)
    (N W m cap reserve F U : ℕ) : ℝ :=
  4 * ((globalActualInteriorLowCensusBound D N W m cap U : ℝ) +
    globalActualInteriorHighDecayCensusBound D N W m cap F reserve) +
  4 * enumeratedWindowCount D.positiveEnumeration N W *
    (F + 4 * globalActualInteriorBlockScaleCap D N W cap) +
  enumeratedWindowCount D.positiveEnumeration N W *
    globalActualInteriorAssemblyLoss D N W m cap reserve

/-- All four actual window classes assembled into one finite inequality.
Every term on the right is a window-level quantity or an explicit census;
all dependent source, graph, endpoint, and prefix fibres have been removed. -/
theorem globalActualFourClassMass_cast_le (D : CarrySeries)
    {N W m cap reserve F U : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : globalActualInteriorUniformCoalescenceEnvelope
      D N W m cap U F < (D.base : ℝ) ^ F) :
    (forwardSpanMass D.positiveEnumeration N W m : ℝ) ≤
      (globalActualShortMassBound D N W m cap reserve : ℝ) +
      ((globalActualRareMassBound D N W m cap : ℝ) +
        (globalActualExteriorCensusBound D hgeom hW hscale
            hpositiveFrom
              (globalActualInteriorThreshold D N W m cap reserve) +
          globalActualInteriorAssembledBound
            D N W m cap reserve F U)) := by
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let shortMass : ℕ :=
    ∑ k ∈ globalActualShortWindowIndices D N W m cap reserve,
      forwardSpan D.positiveEnumeration k m
  let rareMass : ℕ :=
    ∑ k ∈ globalActualRareWindowIndices D N W m,
      forwardSpan D.positiveEnumeration k m
  let exteriorMass : ℕ :=
    ∑ k ∈ globalActualExteriorEligibleWindowIndices
        D hgeom hW hscale hpositiveFrom threshold,
      forwardSpan D.positiveEnumeration k m
  let interiorMass : ℕ :=
    ∑ k ∈ globalActualInteriorOnlyWindowIndices
        D hgeom hW hscale hpositiveFrom threshold,
      forwardSpan D.positiveEnumeration k m
  have hfour := globalActualForwardSpanMass_le_fourClassMasses
    D hgeom hW hscale hpositiveFrom (reserve := reserve)
  change forwardSpanMass D.positiveEnumeration N W m ≤
      shortMass + (rareMass + (exteriorMass + interiorMass)) at hfour
  have hfourReal : (forwardSpanMass D.positiveEnumeration N W m : ℝ) ≤
      (shortMass : ℝ) +
        ((rareMass : ℝ) + ((exteriorMass : ℝ) + (interiorMass : ℝ))) := by
    exact_mod_cast hfour
  have hshort : shortMass ≤ globalActualShortMassBound
      D N W m cap reserve := by
    simpa only [shortMass, globalActualShortMassBound] using
      globalActualShortWindowMass_le D N W m cap reserve
  have hshortReal : (shortMass : ℝ) ≤
      globalActualShortMassBound D N W m cap reserve := by
    exact_mod_cast hshort
  have hrare : rareMass ≤ globalActualRareMassBound D N W m cap := by
    simpa only [rareMass, globalActualRareMassBound] using
      globalActualRareWindowMass_le D hgeom
  have hrareReal : (rareMass : ℝ) ≤
      globalActualRareMassBound D N W m cap := by
    exact_mod_cast hrare
  have hexterior : (exteriorMass : ℝ) ≤
      globalActualExteriorCensusBound D hgeom hW hscale
        hpositiveFrom threshold := by
    rw [show exteriorMass = globalActualExteriorEligibleMass
        D hgeom hW hscale hpositiveFrom threshold by
      simpa only [exteriorMass] using
        globalActualExteriorEligibleWindowMass_eq
          D hgeom hW hscale hpositiveFrom]
    exact globalActualExteriorEligibleMass_cast_le_census
      D hd hw hgeom hW hscale hpositiveFrom
  have hinteriorNat :=
    globalActualInteriorOnlyWindowMass_le_stabilized_add_loss
      D hgeom hW hscale hpositiveFrom hw (reserve := reserve)
  change interiorMass ≤
      globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom threshold +
      enumeratedWindowCount D.positiveEnumeration N W *
        globalActualInteriorAssemblyLoss D N W m cap reserve at hinteriorNat
  have hinteriorBase : (interiorMass : ℝ) ≤
      (globalActualInteriorEligibleStabilizedMass D hgeom hW hscale
        hpositiveFrom threshold : ℝ) +
      enumeratedWindowCount D.positiveEnumeration N W *
        globalActualInteriorAssemblyLoss D N W m cap reserve := by
    exact_mod_cast hinteriorNat
  have heligible :=
    globalActualInteriorEligibleStabilizedMass_cast_le_decay_add_terminal
      D hgeom hW hscale hpositiveFrom hd hw hU hF henvelope
      (reserve := reserve) (F := F)
  have hinterior : (interiorMass : ℝ) ≤
      globalActualInteriorAssembledBound D N W m cap reserve F U := by
    unfold globalActualInteriorAssembledBound
    exact hinteriorBase.trans (add_le_add heligible (le_refl _))
  exact hfourReal.trans (add_le_add hshortReal
    (add_le_add hrareReal (add_le_add hexterior hinterior)))

/-! ## Window-level census envelopes

The finite master inequality above still displays one dependent exterior sum.
The following envelopes remove that last dependency.  They are deliberately
coarse: their purpose is to expose a small list of elementary functions whose
uniform asymptotics can be checked once in the proof of `thm_main_uniform`. -/

/-- Common positive-word census containing every realized locking prefix. -/
def globalActualPrefixWordCensus (D : CarrySeries)
    (N m cap : ℕ) : ℕ :=
  (boundedPositiveGapWords (lockingThreshold D N + cap) m).card

/-- Uniform census for the state-determined part before strict exterior exit. -/
def globalActualPreExteriorCensus (m cap : ℕ) : ℕ :=
  (m + 1) * (1 + cap * 2 ^ m)

/-- Uniform census for the selected strictly exterior continuation word. -/
def globalActualSelectedExteriorCensus
    (threshold m cap : ℕ) : ℕ :=
  (boundedPositiveGapWords (threshold + cap) m).card

/-- Every canonical nonrare prefix lies in the common positive-word census. -/
theorem canonicalNonrarePrefixes_card_le_prefixWordCensus (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap) :
    (canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card ≤
      globalActualPrefixWordCensus D N m cap := by
  calc
    (canonicalNonrarePrefixes D N W m (lockingThreshold D N)).card ≤
        (realizedLockingPrefixes D.positiveEnumeration N W m
          (lockingThreshold D N)).card := by
      exact Finset.card_filter_le _ _
    _ ≤ (boundedPositiveGapWords
          (lockingThreshold D N + cap) m).card :=
      realizedLockingPrefixes_card_le D.positiveEnumeration hgeom
    _ = globalActualPrefixWordCensus D N m cap := rfl

/-- The same census also contains the rare prefix family. -/
theorem globalActualRarePrefixes_card_le_prefixWordCensus (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap) :
    (globalActualRarePrefixes D N W m).card ≤
      globalActualPrefixWordCensus D N m cap := by
  calc
    (globalActualRarePrefixes D N W m).card ≤
        (realizedLockingPrefixes D.positiveEnumeration N W m
          (lockingThreshold D N)).card := by
      exact Finset.card_filter_le _ _
    _ ≤ (boundedPositiveGapWords
          (lockingThreshold D N + cap) m).card :=
      realizedLockingPrefixes_card_le D.positiveEnumeration hgeom
    _ = globalActualPrefixWordCensus D N m cap := rfl

/-- Cardinal form of the proved binary-branching pre-exterior census. -/
theorem preExteriorRecord_card_le_census (D : CarrySeries)
    (cap m : ℕ) (μ : ℝ) :
    Fintype.card (PreExteriorRecord D.base cap m μ) ≤
      globalActualPreExteriorCensus m cap := by
  rw [globalActualPreExteriorCensus, Fintype.card_coe]
  exact boundedPreExteriorCandidates_card_le D.base_ge_two μ

/-- The selected exterior record type has exactly the advertised word count. -/
theorem selectedExteriorRecord_card_eq_census
    (threshold m cap : ℕ) :
    Fintype.card (SelectedExteriorRecord cap threshold m) =
      globalActualSelectedExteriorCensus threshold m cap := by
  simp only [globalActualSelectedExteriorCensus, SelectedExteriorRecord,
    Fintype.card_coe]

/-- Every canonical graph's integral top-state scale is bounded by the common
state denominator cap. -/
theorem canonicalLockedGraph_topStateScale_le_cap (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : CanonicalNonrarePrefix D N W m (lockingThreshold D N)) :
    (canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx).topStateScale
        D.denominator D.weight ≤
      globalActualInteriorStateDenominatorCap D N W cap := by
  let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx
  have hden : G.denominator ≤
      (W + lockingThreshold D N + cap) ^
        vandermondeExponent D.weight.natDegree := by
    simpa only [G] using
      canonicalLockedGraph_den_le D hgeom hW hscale hpositiveFrom pfx
  unfold PolynomialGraph.topStateScale
    globalActualInteriorStateDenominatorCap
  calc
    G.denominator * D.denominator *
        (D.weight.coeff D.weight.natDegree).natAbs =
      G.denominator *
        (D.denominator * (D.weight.coeff D.weight.natDegree).natAbs) := by
          ring
    _ ≤ (W + lockingThreshold D N + cap) ^
          vandermondeExponent D.weight.natDegree *
        (D.denominator * (D.weight.coeff D.weight.natDegree).natAbs) :=
      Nat.mul_le_mul_right _ hden
    _ = (W + lockingThreshold D N + cap) ^
          vandermondeExponent D.weight.natDegree * D.denominator *
        (D.weight.coeff D.weight.natDegree).natAbs := by ring

/-- Uniform polynomial-sublevel fibre factor after replacing the graph scale
by its common window cap. -/
noncomputable def globalActualExteriorFibreEnvelope (D : CarrySeries)
    (N W m cap threshold : ℕ) : ℝ :=
  D.weight.natDegree + 2 * D.weight.natDegree *
    (((D.heightNatConstant * (N + W + m * cap + 1) ^
          D.weight.natDegree : ℕ) : ℝ) *
        (globalActualInteriorStateDenominatorCap D N W cap : ℝ) *
        (D.base - 1 : ℝ) /
      (D.base : ℝ) ^ threshold) ^
        (((D.weight.natDegree : ℝ))⁻¹)

theorem globalActualExteriorFibreEnvelope_nonneg (D : CarrySeries)
    (N W m cap threshold : ℕ) :
    0 ≤ globalActualExteriorFibreEnvelope D N W m cap threshold := by
  have hbase : (1 : ℝ) ≤ D.base := by
    exact_mod_cast (show 1 ≤ D.base from
      (by exact (show 1 ≤ 2 by decide).trans D.base_ge_two))
  unfold globalActualExteriorFibreEnvelope
  positivity

/-- Completely window-level exterior census envelope. -/
noncomputable def globalActualExteriorCoarseBound (D : CarrySeries)
    (N W m cap threshold : ℕ) : ℝ :=
  (globalActualPrefixWordCensus D N m cap : ℝ) *
    globalActualPreExteriorCensus m cap *
    globalActualSelectedExteriorCensus threshold m cap *
    globalActualExteriorFibreEnvelope D N W m cap threshold *
    (m * cap : ℕ)

/-- The dependent exterior census is bounded by the explicit window envelope. -/
theorem globalActualExteriorCensusBound_le_coarse (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N) (threshold : ℕ) :
    globalActualExteriorCensusBound D hgeom hW hscale hpositiveFrom threshold ≤
      globalActualExteriorCoarseBound D N W m cap threshold := by
  classical
  let prefixes := (canonicalNonrarePrefixes D N W m
    (lockingThreshold D N)).attach
  let perPrefix : ℝ :=
    globalActualPreExteriorCensus m cap *
      globalActualSelectedExteriorCensus threshold m cap *
      globalActualExteriorFibreEnvelope D N W m cap threshold *
      (m * cap : ℕ)
  have hterm (pfx : CanonicalNonrarePrefix D N W m
      (lockingThreshold D N)) :
      let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx
      (Fintype.card (PreExteriorRecord D.base cap m
          (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
        (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) *
        (D.weight.natDegree + 2 * D.weight.natDegree *
          (((D.heightNatConstant * (N + W + m * cap + 1) ^
                D.weight.natDegree : ℕ) : ℝ) *
              ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
              (D.base - 1 : ℝ) /
            (D.base : ℝ) ^ threshold) ^
              (((D.weight.natDegree : ℝ))⁻¹)) *
        (m * cap : ℕ) ≤ perPrefix := by
    dsimp only
    let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx
    have hpreNat := preExteriorRecord_card_le_census D cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    have hpre :
        (Fintype.card (PreExteriorRecord D.base cap m
          (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) ≤
            globalActualPreExteriorCensus m cap := by
      exact_mod_cast hpreNat
    have hselected :
        (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) =
          globalActualSelectedExteriorCensus threshold m cap := by
      exact_mod_cast selectedExteriorRecord_card_eq_census threshold m cap
    have htopNat : G.topStateScale D.denominator D.weight ≤
        globalActualInteriorStateDenominatorCap D N W cap := by
      simpa only [G] using canonicalLockedGraph_topStateScale_le_cap
        D hgeom hW hscale hpositiveFrom pfx
    have htop : (G.topStateScale D.denominator D.weight : ℝ) ≤
        globalActualInteriorStateDenominatorCap D N W cap := by
      exact_mod_cast htopNat
    have hbase : (1 : ℝ) ≤ D.base := by
      exact_mod_cast (show 1 ≤ D.base from
        (by exact (show 1 ≤ 2 by decide).trans D.base_ge_two))
    have hfibre :
        D.weight.natDegree + 2 * D.weight.natDegree *
            (((D.heightNatConstant * (N + W + m * cap + 1) ^
                  D.weight.natDegree : ℕ) : ℝ) *
                ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
                (D.base - 1 : ℝ) /
              (D.base : ℝ) ^ threshold) ^
                (((D.weight.natDegree : ℝ))⁻¹) ≤
          globalActualExteriorFibreEnvelope D N W m cap threshold := by
      unfold globalActualExteriorFibreEnvelope
      gcongr
    rw [hselected]
    dsimp only [perPrefix]
    have hpreselected :
        (Fintype.card (PreExteriorRecord D.base cap m
            (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
            globalActualSelectedExteriorCensus threshold m cap ≤
          globalActualPreExteriorCensus m cap *
            globalActualSelectedExteriorCensus threshold m cap :=
      mul_le_mul_of_nonneg_right hpre (by positivity)
    have hrawFibre : 0 ≤
        D.weight.natDegree + 2 * D.weight.natDegree *
          (((D.heightNatConstant * (N + W + m * cap + 1) ^
                D.weight.natDegree : ℕ) : ℝ) *
              ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
              (D.base - 1 : ℝ) /
            (D.base : ℝ) ^ threshold) ^
              (((D.weight.natDegree : ℝ))⁻¹) := by
      positivity
    have htriple :
        (Fintype.card (PreExteriorRecord D.base cap m
            (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
            globalActualSelectedExteriorCensus threshold m cap *
            (D.weight.natDegree + 2 * D.weight.natDegree *
              (((D.heightNatConstant * (N + W + m * cap + 1) ^
                    D.weight.natDegree : ℕ) : ℝ) *
                  ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
                  (D.base - 1 : ℝ) /
                (D.base : ℝ) ^ threshold) ^
                  (((D.weight.natDegree : ℝ))⁻¹)) ≤
          globalActualPreExteriorCensus m cap *
            globalActualSelectedExteriorCensus threshold m cap *
            globalActualExteriorFibreEnvelope D N W m cap threshold := by
      calc
        _ ≤ (globalActualPreExteriorCensus m cap *
              globalActualSelectedExteriorCensus threshold m cap) *
            (D.weight.natDegree + 2 * D.weight.natDegree *
              (((D.heightNatConstant * (N + W + m * cap + 1) ^
                    D.weight.natDegree : ℕ) : ℝ) *
                  ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
                  (D.base - 1 : ℝ) /
                (D.base : ℝ) ^ threshold) ^
                  (((D.weight.natDegree : ℝ))⁻¹)) :=
          mul_le_mul_of_nonneg_right hpreselected hrawFibre
        _ ≤ _ := mul_le_mul_of_nonneg_left hfibre (by positivity)
    have hfull := mul_le_mul_of_nonneg_right htriple
      (show (0 : ℝ) ≤ (m * cap : ℕ) by positivity)
    simpa only [G] using hfull
  unfold globalActualExteriorCensusBound
  change (∑ pfx ∈ prefixes, _) ≤ _
  calc
    (∑ pfx ∈ prefixes,
        let G := canonicalLockedGraph D hgeom hW hscale hpositiveFrom pfx
        (Fintype.card (PreExteriorRecord D.base cap m
          (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
        (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) *
        (D.weight.natDegree + 2 * D.weight.natDegree *
          (((D.heightNatConstant * (N + W + m * cap + 1) ^
                D.weight.natDegree : ℕ) : ℝ) *
              ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
              (D.base - 1 : ℝ) /
            (D.base : ℝ) ^ threshold) ^
              (((D.weight.natDegree : ℝ))⁻¹)) *
        (m * cap : ℕ)) ≤ ∑ _pfx ∈ prefixes, perPrefix := by
      exact Finset.sum_le_sum fun pfx _ => hterm pfx
    _ = (prefixes.card : ℝ) * perPrefix := by simp
    _ ≤ (globalActualPrefixWordCensus D N m cap : ℝ) * perPrefix := by
      have hperPrefix : 0 ≤ perPrefix := by
        dsimp only [perPrefix]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity)
              (by positivity))
            (globalActualExteriorFibreEnvelope_nonneg
              D N W m cap threshold))
          (by positivity)
      apply mul_le_mul_of_nonneg_right _ hperPrefix
      have hprefNat : prefixes.card ≤
          globalActualPrefixWordCensus D N m cap := by
        simpa only [prefixes, Finset.card_attach] using
          canonicalNonrarePrefixes_card_le_prefixWordCensus D hgeom
      exact_mod_cast hprefNat
    _ = globalActualExteriorCoarseBound D N W m cap threshold := by
      unfold globalActualExteriorCoarseBound
      dsimp only [prefixes, perPrefix]
      ring

/-- Rare-prefix mass with the realized prefix family replaced by its common
word census. -/
def globalActualRareCoarseBound (D : CarrySeries)
    (N m cap : ℕ) : ℕ :=
  globalActualPrefixWordCensus D N m cap *
    (D.weight.natDegree + 1) * (m * cap)

theorem globalActualRareMassBound_le_coarse (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap) :
    globalActualRareMassBound D N W m cap ≤
      globalActualRareCoarseBound D N m cap := by
  unfold globalActualRareMassBound globalActualRareCoarseBound
  gcongr
  exact globalActualRarePrefixes_card_le_prefixWordCensus D hgeom

/-- Low-frequency interior census with its realized prefix cardinality removed. -/
def globalActualInteriorLowCoarseBound (D : CarrySeries)
    (N W m cap U : ℕ) : ℕ :=
  (globalActualPrefixWordCensus D N m cap *
      (m + 1) * (Nat.log 2 cap + 1)) *
    (U * (m + 1) *
      (4 * globalActualInteriorBlockScaleCap D N W cap))

theorem globalActualInteriorLowCensusBound_le_coarse (D : CarrySeries)
    {N W m cap U : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap) :
    globalActualInteriorLowCensusBound D N W m cap U ≤
      globalActualInteriorLowCoarseBound D N W m cap U := by
  unfold globalActualInteriorLowCensusBound
    globalActualInteriorLowCoarseBound
  gcongr
  exact canonicalNonrarePrefixes_card_le_prefixWordCensus D hgeom

/-! ## A single coarse contradiction budget -/

/-- Interior part of the coarse contradiction budget. -/
noncomputable def globalActualInteriorCoarseBound (D : CarrySeries)
    (N W m cap reserve F U : ℕ) : ℝ :=
  4 * ((globalActualInteriorLowCoarseBound D N W m cap U : ℝ) +
    globalActualInteriorHighDecayCensusBound D N W m cap F reserve) +
  4 * enumeratedWindowCount D.positiveEnumeration N W *
    (F + 4 * globalActualInteriorBlockScaleCap D N W cap) +
  enumeratedWindowCount D.positiveEnumeration N W *
    globalActualInteriorAssemblyLoss D N W m cap reserve

/-- All four class bounds together with the endpoint loss from the window-mass
identity.  Every term is now independent of a realized prefix or graph. -/
noncomputable def globalActualFourClassCoarseError (D : CarrySeries)
    (N W m cap reserve F U : ℕ) : ℝ :=
  (globalActualShortMassBound D N W m cap reserve : ℝ) +
    ((globalActualRareCoarseBound D N m cap : ℝ) +
      (globalActualExteriorCoarseBound D N W m cap
          (globalActualInteriorThreshold D N W m cap reserve) +
        globalActualInteriorCoarseBound D N W m cap reserve F U)) +
    (m * m * cap : ℕ)

theorem globalActualInteriorAssembledBound_le_coarse (D : CarrySeries)
    {N W m cap reserve F U : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap) :
    globalActualInteriorAssembledBound D N W m cap reserve F U ≤
      globalActualInteriorCoarseBound D N W m cap reserve F U := by
  have hlowNat := globalActualInteriorLowCensusBound_le_coarse
    D (U := U) hgeom
  have hlow :
      (globalActualInteriorLowCensusBound D N W m cap U : ℝ) ≤
        globalActualInteriorLowCoarseBound D N W m cap U := by
    exact_mod_cast hlowNat
  unfold globalActualInteriorAssembledBound globalActualInteriorCoarseBound
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (add_le_add hlow (le_refl _)) (by positivity))
      (le_refl _))
    (le_refl _)

/-- The finite four-class theorem and the mass identity reduce every positive
degree window to one explicit inequality `mW ≤ coarseError`. -/
theorem globalActualMassScale_le_coarseError (D : CarrySeries)
    {N W m cap reserve F U : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : globalActualInteriorUniformCoalescenceEnvelope
      D N W m cap U F < (D.base : ℝ) ^ F) :
    (m * W : ℕ) ≤
      globalActualFourClassCoarseError D N W m cap reserve F U := by
  have hmaster := globalActualFourClassMass_cast_le D hgeom hW hscale
    hpositiveFrom hd hw hU hF henvelope (reserve := reserve)
  have hrareNat := globalActualRareMassBound_le_coarse D hgeom
  have hrare : (globalActualRareMassBound D N W m cap : ℝ) ≤
      globalActualRareCoarseBound D N m cap := by
    exact_mod_cast hrareNat
  have hext := globalActualExteriorCensusBound_le_coarse
    D hgeom hW hscale hpositiveFrom
      (globalActualInteriorThreshold D N W m cap reserve)
  have hinterior := globalActualInteriorAssembledBound_le_coarse
    D (reserve := reserve) (F := F) (U := U) hgeom
  have hforward :
      (forwardSpanMass D.positiveEnumeration N W m : ℝ) ≤
        (globalActualShortMassBound D N W m cap reserve : ℝ) +
          ((globalActualRareCoarseBound D N m cap : ℝ) +
            (globalActualExteriorCoarseBound D N W m cap
                (globalActualInteriorThreshold D N W m cap reserve) +
              globalActualInteriorCoarseBound
                D N W m cap reserve F U)) := by
    exact hmaster.trans (add_le_add (le_refl _)
      (add_le_add hrare (add_le_add hext hinterior)))
  have hmassNat := WindowGeometry.mass_lower D.positiveEnumeration hgeom
  have hmass : (m * W : ℕ) ≤
      (forwardSpanMass D.positiveEnumeration N W m : ℝ) +
        (m * m * cap : ℕ) := by
    exact_mod_cast hmassNat
  exact hmass.trans <| by
    unfold globalActualFourClassCoarseError
    exact add_le_add hforward (le_refl _)

/-- Contradiction-ready form of the coarse master inequality. -/
theorem not_globalActualFourClassCoarseError_lt_massScale (D : CarrySeries)
    {N W m cap reserve F U : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N) (hscale : lockingThreshold D N + cap ≤ N)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hU : 2 * D.weight.natDegree + 1 ≤ U)
    (hF : D.weight.natDegree ≤ F)
    (henvelope : globalActualInteriorUniformCoalescenceEnvelope
      D N W m cap U F < (D.base : ℝ) ^ F) :
    ¬ globalActualFourClassCoarseError D N W m cap reserve F U <
      (m * W : ℕ) :=
  not_lt_of_ge <| globalActualMassScale_le_coarseError D hgeom hW hscale
    hpositiveFrom hd hw hU hF henvelope

/-! ## Canonical logarithmic envelopes -/

/-- One discrete base-`b` logarithmic scale dominating every occurrence of
`log_b(cN+1)` in the finite argument. -/
def globalActualLogScale (D : CarrySeries) (N : ℕ) : ℕ :=
  Nat.log D.base (3 * N + 1) + 1

theorem globalActualLogScale_pos (D : CarrySeries) (N : ℕ) :
    0 < globalActualLogScale D N := by
  unfold globalActualLogScale
  omega

theorem three_mul_add_one_lt_base_pow_globalActualLogScale
    (D : CarrySeries) (N : ℕ) :
    3 * N + 1 < D.base ^ globalActualLogScale D N := by
  simpa only [globalActualLogScale, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self
      (lt_of_lt_of_le (by decide : 1 < 2) D.base_ge_two) (3 * N + 1)

theorem self_lt_base_pow_globalActualLogScale
    (D : CarrySeries) (N : ℕ) :
    N < D.base ^ globalActualLogScale D N := by
  exact (by omega : N < 3 * N + 1).trans
    (three_mul_add_one_lt_base_pow_globalActualLogScale D N)

/-- Affine logarithmic envelope for the actual gap cap returned by
`exists_windowGeometry`. -/
def globalActualGapEnvelope (D : CarrySeries) (Cgap N : ℕ) : ℕ :=
  D.weight.natDegree * globalActualLogScale D N + Cgap

theorem actualGapCap_le_globalActualGapEnvelope (D : CarrySeries)
    (Cgap N : ℕ) :
    D.weight.natDegree * Nat.log D.base (3 * N) + Cgap ≤
      globalActualGapEnvelope D Cgap N := by
  unfold globalActualGapEnvelope globalActualLogScale
  have hlog : Nat.log D.base (3 * N) ≤
      Nat.log D.base (3 * N + 1) := Nat.log_mono_right (by omega)
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left D.weight.natDegree
      (hlog.trans (Nat.le_add_right _ 1))) Cgap

/-- The canonical logarithmic scale also dominates `log_b N` itself. -/
theorem natLog_le_globalActualLogScale (D : CarrySeries) (N : ℕ) :
    Nat.log D.base N ≤ globalActualLogScale D N := by
  unfold globalActualLogScale
  exact (Nat.log_mono_right (by omega : N ≤ 3 * N + 1)).trans
    (Nat.le_add_right _ 1)

/-- The locking threshold is exactly affine in the common log scale. -/
theorem lockingThreshold_eq_globalActualLogScale (D : CarrySeries) (N : ℕ) :
    lockingThreshold D N =
      Nat.clog D.base (lockingPolynomialConstant D + 1) +
        lockingPolynomialExponent D * globalActualLogScale D N := by
  rfl

/-- Dyadic exponent dominating the full normalized-state denominator cap. -/
def globalActualStatePowerExponent (D : CarrySeries) (N : ℕ) : ℕ :=
  Nat.clog 2
      (2 ^ vandermondeExponent D.weight.natDegree * D.denominator *
        (D.weight.coeff D.weight.natDegree).natAbs) +
    Nat.clog 2 D.base *
      (globalActualLogScale D N *
        vandermondeExponent D.weight.natDegree)

/-- Under the elementary window-scale conditions the state denominator is
bounded by one explicit power of two. -/
theorem globalActualInteriorStateDenominatorCap_le_two_pow (D : CarrySeries)
    {N W cap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N) :
    globalActualInteriorStateDenominatorCap D N W cap ≤
      2 ^ globalActualStatePowerExponent D N := by
  let s := vandermondeExponent D.weight.natDegree
  let L := globalActualLogScale D N
  let kb := Nat.clog 2 D.base
  let C := 2 ^ s * D.denominator *
    (D.weight.coeff D.weight.natDegree).natAbs
  have hsum : W + lockingThreshold D N + cap ≤ 2 * N := by omega
  have hN : N ≤ D.base ^ L := by
    exact (self_lt_base_pow_globalActualLogScale D N).le
  have hbpow : D.base ≤ 2 ^ kb := by
    dsimp only [kb]
    exact Nat.le_pow_clog (by decide : 1 < 2) D.base
  have hNpow : N ^ s ≤ 2 ^ (kb * (L * s)) := by
    calc
      N ^ s ≤ (D.base ^ L) ^ s := Nat.pow_le_pow_left hN s
      _ = D.base ^ (L * s) := by rw [Nat.pow_mul]
      _ ≤ (2 ^ kb) ^ (L * s) :=
        Nat.pow_le_pow_left hbpow (L * s)
      _ = 2 ^ (kb * (L * s)) := by
        simp only [← pow_mul]
  have hC : C ≤ 2 ^ Nat.clog 2 C :=
    Nat.le_pow_clog (by decide : 1 < 2) C
  unfold globalActualInteriorStateDenominatorCap
  change (W + lockingThreshold D N + cap) ^ s * D.denominator *
      (D.weight.coeff D.weight.natDegree).natAbs ≤
    2 ^ globalActualStatePowerExponent D N
  calc
    (W + lockingThreshold D N + cap) ^ s * D.denominator *
        (D.weight.coeff D.weight.natDegree).natAbs ≤
      (2 * N) ^ s * D.denominator *
        (D.weight.coeff D.weight.natDegree).natAbs := by gcongr
    _ = C * N ^ s := by
      dsimp only [C]
      rw [Nat.mul_pow]
      ring
    _ ≤ 2 ^ Nat.clog 2 C * 2 ^ (kb * (L * s)) :=
      Nat.mul_le_mul hC hNpow
    _ = 2 ^ (Nat.clog 2 C + kb * (L * s)) := by rw [pow_add]
    _ = 2 ^ globalActualStatePowerExponent D N := by
      rfl

theorem globalActualInteriorStateLog_le_powerExponent (D : CarrySeries)
    {N W cap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N) :
    Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) ≤
      globalActualStatePowerExponent D N := by
  exact (Nat.log_le_clog 2 _).trans
    (Nat.clog_le_of_le_pow
      (globalActualInteriorStateDenominatorCap_le_two_pow D hW hscale))

/-- Affine upper envelope for every logarithmic interior block scale. -/
def globalActualBlockScaleEnvelope (D : CarrySeries) (N : ℕ) : ℕ :=
  2 + globalActualStatePowerExponent D N

theorem globalActualInteriorBlockScaleCap_le_envelope (D : CarrySeries)
    {N W cap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N) :
    globalActualInteriorBlockScaleCap D N W cap ≤
      globalActualBlockScaleEnvelope D N := by
  have hstate := globalActualInteriorStateDenominatorCap_le_two_pow
    D hW hscale
  have hfour :
      4 * globalActualInteriorStateDenominatorCap D N W cap ≤
        2 ^ globalActualBlockScaleEnvelope D N := by
    calc
      4 * globalActualInteriorStateDenominatorCap D N W cap ≤
          4 * 2 ^ globalActualStatePowerExponent D N :=
        Nat.mul_le_mul_left 4 hstate
      _ = 2 ^ (2 + globalActualStatePowerExponent D N) := by
        rw [pow_add]
        norm_num
      _ = 2 ^ globalActualBlockScaleEnvelope D N := rfl
  unfold globalActualInteriorBlockScaleCap logarithmicBlockScale
  calc
    Nat.clog D.base
        (4 * globalActualInteriorStateDenominatorCap D N W cap) ≤
      Nat.clog 2
        (4 * globalActualInteriorStateDenominatorCap D N W cap) :=
      Nat.clog_anti_left (by decide : 1 < 2) D.base_ge_two
    _ ≤ globalActualBlockScaleEnvelope D N :=
      Nat.clog_le_of_le_pow hfour

/-- Affine envelope for the canonical coalescence continuation span. -/
def globalActualContinuationEnvelope (D : CarrySeries) (N : ℕ) : ℕ :=
  Nat.clog D.base
      (globalActualInteriorCoalescencePolynomialConstant D + 1) +
    globalActualInteriorCoalescencePolynomialExponent D *
      (globalActualLogScale D N + 1)

theorem globalActualInteriorContinuationSpan_le_envelope (D : CarrySeries)
    (N : ℕ) :
    globalActualInteriorContinuationSpan D N ≤
      globalActualContinuationEnvelope D N := by
  have hfive : 5 * N + 1 <
      D.base ^ (globalActualLogScale D N + 1) := by
    calc
      5 * N + 1 ≤ 2 * (3 * N + 1) := by omega
      _ < 2 * D.base ^ globalActualLogScale D N :=
        Nat.mul_lt_mul_of_pos_left
          (three_mul_add_one_lt_base_pow_globalActualLogScale D N)
          (by norm_num)
      _ ≤ D.base * D.base ^ globalActualLogScale D N :=
        Nat.mul_le_mul_right _ D.base_ge_two
      _ = D.base ^ (globalActualLogScale D N + 1) := by
        rw [pow_succ']
  have hlog : Nat.log D.base (5 * N + 1) + 1 ≤
      globalActualLogScale D N + 1 := by
    have hlt : Nat.log D.base (5 * N + 1) <
        globalActualLogScale D N + 1 :=
      Nat.log_lt_of_lt_pow (by omega) hfive
    omega
  unfold globalActualInteriorContinuationSpan
    globalActualContinuationEnvelope
  gcongr

/-- Complete stabilization threshold bounded only by the common logarithmic
envelopes and the chosen reserve. -/
def globalActualThresholdEnvelope (D : CarrySeries)
    (Cgap N m reserve : ℕ) : ℕ :=
  globalActualStatePowerExponent D N +
    2 * globalActualGapEnvelope D Cgap N +
    24 * globalActualBlockScaleEnvelope D N + reserve * m

theorem globalActualInteriorThreshold_le_envelope (D : CarrySeries)
    {N W m cap reserve Cgap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (hcap : cap ≤ globalActualGapEnvelope D Cgap N) :
    globalActualInteriorThreshold D N W m cap reserve ≤
      globalActualThresholdEnvelope D Cgap N m reserve := by
  unfold globalActualInteriorThreshold globalActualThresholdEnvelope
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (globalActualInteriorStateLog_le_powerExponent D hW hscale)
        (Nat.mul_le_mul_left 2 hcap))
      (Nat.mul_le_mul_left 24
        (globalActualInteriorBlockScaleCap_le_envelope D hW hscale)))
    (le_refl _)

/-! ## Small-entropy multiplicities -/

theorem binaryEntropy_nonneg_on_unit {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ Erdos260.binaryEntropy α := by
  have hentropyEq : Erdos260.binaryEntropy α =
      Real.binEntropy α / Real.log 2 := by
    rw [Erdos260.binaryEntropy,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog, Real.logb]
    ring
  rw [hentropyEq]
  exact div_nonneg (Real.binEntropy_nonneg hα0 hα1)
    (Real.log_nonneg (by norm_num))

/-- A large natural divisor makes both the binary branching exponent and the
composition entropy arbitrarily small. -/
theorem exists_entropy_divisor (C ε : ℝ)
    (_hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ K : ℕ, 4 ≤ K ∧
      C * Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ ε ∧
      1 / (K : ℝ) ≤ ε := by
  have harg : Tendsto (fun K : ℕ => (2 : ℝ) / (K : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hzero : Erdos260.binaryEntropy 0 = 0 := by
    simp [Erdos260.binaryEntropy]
  have hentropy : Tendsto
      (fun K : ℕ => Erdos260.binaryEntropy (2 / (K : ℝ)))
      atTop (𝓝 0) := by
    change Tendsto (Erdos260.binaryEntropy ∘
      fun K : ℕ => (2 : ℝ) / (K : ℝ)) atTop (𝓝 0)
    simpa only [hzero] using
      Erdos260.binaryEntropy_continuous.tendsto 0 |>.comp harg
  have hscaled : Tendsto
      (fun K : ℕ => C * Erdos260.binaryEntropy (2 / (K : ℝ)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hentropy
  have hinv : Tendsto (fun K : ℕ => (1 : ℝ) / (K : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ K : ℕ in atTop,
      C * Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ ε ∧
        1 / (K : ℝ) ≤ ε ∧ 4 ≤ K :=
    (hscaled.eventually (eventually_le_nhds hε)).and <|
      (hinv.eventually (eventually_le_nhds hε)).and
        (eventually_ge_atTop 4)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hevent
  have h := hK₀ K₀ le_rfl
  exact ⟨K₀, h.2.2, h.1, h.2.1⟩

/-- Canonical number of consecutive support gaps used at scale `N`. -/
def globalActualMultiplicity (D : CarrySeries) (K N : ℕ) : ℕ :=
  globalActualLogScale D N / K

/-- Finite entropy estimate specialized to the canonical multiplicity.  It
only asks for upper and lower linear bounds on the word span. -/
theorem boundedPositiveGapWords_card_le_logScale_entropy
    (D : CarrySeries) {N H C K : ℕ} {ε : ℝ}
    (hK : 4 ≤ K) (hKL : K ≤ globalActualLogScale D N)
    (hHlower : globalActualLogScale D N ≤ H + 1)
    (hHupper : H + 1 ≤ C * globalActualLogScale D N)
    (hentropy : (C : ℝ) *
      Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ ε) :
    ((boundedPositiveGapWords H
        (globalActualMultiplicity D K N)).card : ℝ) ≤
      ((C * globalActualLogScale D N : ℕ) : ℝ) ^ 2 *
        Real.rpow 2 (ε * globalActualLogScale D N) := by
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  let α : ℝ := 2 / K
  have hKpos : 0 < K := by omega
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hLreal : (K : ℝ) ≤ L := by exact_mod_cast hKL
  have hα0 : 0 < α := by dsimp only [α]; positivity
  have hαhalf : α ≤ 1 / 2 := by
    dsimp only [α]
    rw [div_le_iff₀ hKreal]
    have hKrealFour : (4 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hαone : α ≤ 1 := hαhalf.trans (by norm_num)
  have hentropy0 : 0 ≤ Erdos260.binaryEntropy α :=
    binaryEntropy_nonneg_on_unit hα0.le hαone
  have hmCast : (m : ℝ) ≤ (L : ℝ) / K := by
    dsimp only [m, globalActualMultiplicity]
    exact Nat.cast_div_le
  have honeDiv : (1 : ℝ) ≤ (L : ℝ) / K := by
    rw [le_div_iff₀ hKreal]
    simpa only [one_mul] using hLreal
  have hmOne : ((m + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) / K := by
    push_cast
    calc
      (m : ℝ) + 1 ≤ (L : ℝ) / K + 1 := by
        simpa only [add_comm] using add_le_add_right hmCast 1
      _ ≤ (L : ℝ) / K + (L : ℝ) / K := by
        simpa only [add_comm] using
          add_le_add_left honeDiv ((L : ℝ) / K)
      _ = 2 * (L : ℝ) / K := by ring
  have hratio : ((m + 1 : ℕ) : ℝ) ≤ α * (H + 1 : ℕ) := by
    have hLowerReal : (L : ℝ) ≤ (H + 1 : ℕ) := by
      exact_mod_cast hHlower
    calc
      ((m + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) / K := hmOne
      _ = α * (L : ℝ) := by dsimp only [α]; field_simp
      _ ≤ α * (H + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hLowerReal hα0.le
  have hHtwo : 2 ≤ H + 1 := by
    have : 4 ≤ L := hK.trans hKL
    omega
  have hraw := eq_prefixcount_entropy H m α hHtwo hα0 hαhalf hratio
  have hUpperReal : ((H + 1 : ℕ) : ℝ) ≤ ((C * L : ℕ) : ℝ) := by
    exact_mod_cast hHupper
  have hpoly : (((H + 1 : ℕ) : ℝ) ^ 2) ≤
      (((C * L : ℕ) : ℝ) ^ 2) := by gcongr
  have hexponent : ((H + 1 : ℕ) : ℝ) *
      Erdos260.binaryEntropy α ≤ ε * L := by
    calc
      ((H + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α ≤
          ((C * L : ℕ) : ℝ) * Erdos260.binaryEntropy α :=
        mul_le_mul_of_nonneg_right hUpperReal hentropy0
      _ = ((C : ℝ) * Erdos260.binaryEntropy α) * L := by
        push_cast
        ring
      _ ≤ ε * L := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [α] using hentropy
  have hrpow : Real.rpow 2
      (((H + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α) ≤
      Real.rpow 2 (ε * L) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  exact hraw.trans (mul_le_mul hpoly hrpow
    (Real.rpow_nonneg (by norm_num) _) (by positivity))

/-! ## Linearized logarithmic losses -/

theorem nat_const_add_mul_le_mul (a q L : ℕ) (hL : 1 ≤ L) :
    a + q * L ≤ (a + q) * L := by
  have ha : a ≤ a * L := by
    simpa only [mul_one] using Nat.mul_le_mul_left a hL
  calc
    a + q * L ≤ a * L + q * L := Nat.add_le_add_right ha _
    _ = (a + q) * L := by ring

def globalActualStateSlope (D : CarrySeries) : ℕ :=
  Nat.clog 2
      (2 ^ vandermondeExponent D.weight.natDegree * D.denominator *
        (D.weight.coeff D.weight.natDegree).natAbs) +
    Nat.clog 2 D.base * vandermondeExponent D.weight.natDegree

def globalActualBlockSlope (D : CarrySeries) : ℕ :=
  2 + globalActualStateSlope D

def globalActualLockingSlope (D : CarrySeries) : ℕ :=
  Nat.clog D.base (lockingPolynomialConstant D + 1) +
    lockingPolynomialExponent D

def globalActualGapSlope (D : CarrySeries) (Cgap : ℕ) : ℕ :=
  D.weight.natDegree + Cgap

def globalActualContinuationSlope (D : CarrySeries) : ℕ :=
  Nat.clog D.base
      (globalActualInteriorCoalescencePolynomialConstant D + 1) +
    2 * globalActualInteriorCoalescencePolynomialExponent D

def globalActualThresholdSlope (D : CarrySeries)
    (Cgap reserve : ℕ) : ℕ :=
  globalActualStateSlope D + 2 * globalActualGapSlope D Cgap +
    24 * globalActualBlockSlope D + reserve

def globalActualPrefixSpanSlope (D : CarrySeries) (Cgap : ℕ) : ℕ :=
  globalActualLockingSlope D + globalActualGapSlope D Cgap + 1

def globalActualSelectedSpanSlope (D : CarrySeries)
    (Cgap reserve : ℕ) : ℕ :=
  globalActualThresholdSlope D Cgap reserve +
    globalActualGapSlope D Cgap + 1

def globalActualClassificationSlope (D : CarrySeries)
    (Cgap reserve : ℕ) : ℕ :=
  globalActualLockingSlope D + 2 * globalActualGapSlope D Cgap + 1 +
    2 * globalActualThresholdSlope D Cgap reserve

def globalActualAssemblySlope (D : CarrySeries)
    (Cgap reserve : ℕ) : ℕ :=
  globalActualLockingSlope D + 4 * globalActualGapSlope D Cgap + 1 +
    globalActualThresholdSlope D Cgap reserve +
    globalActualStateSlope D

def globalActualTerminalSlope (D : CarrySeries) : ℕ :=
  globalActualContinuationSlope D + 4 * globalActualBlockSlope D

theorem globalActualStatePowerExponent_le_slope_mul (D : CarrySeries)
    (N : ℕ) :
    globalActualStatePowerExponent D N ≤
      globalActualStateSlope D * globalActualLogScale D N := by
  let L := globalActualLogScale D N
  let a := Nat.clog 2
    (2 ^ vandermondeExponent D.weight.natDegree * D.denominator *
      (D.weight.coeff D.weight.natDegree).natAbs)
  let q := Nat.clog 2 D.base *
    vandermondeExponent D.weight.natDegree
  have hL : 1 ≤ L := globalActualLogScale_pos D N
  have h := nat_const_add_mul_le_mul a q L hL
  simpa only [globalActualStatePowerExponent, globalActualStateSlope,
    L, a, q, mul_assoc, mul_left_comm, mul_comm] using h

theorem globalActualBlockScaleEnvelope_le_slope_mul (D : CarrySeries)
    (N : ℕ) :
    globalActualBlockScaleEnvelope D N ≤
      globalActualBlockSlope D * globalActualLogScale D N := by
  let L := globalActualLogScale D N
  have hL : 1 ≤ L := globalActualLogScale_pos D N
  calc
    globalActualBlockScaleEnvelope D N =
        2 + globalActualStatePowerExponent D N := rfl
    _ ≤ 2 + globalActualStateSlope D * L :=
      Nat.add_le_add_left (globalActualStatePowerExponent_le_slope_mul D N) 2
    _ ≤ (2 + globalActualStateSlope D) * L :=
      nat_const_add_mul_le_mul 2 (globalActualStateSlope D) L hL
    _ = globalActualBlockSlope D * globalActualLogScale D N := rfl

theorem lockingThreshold_le_slope_mul (D : CarrySeries) (N : ℕ) :
    lockingThreshold D N ≤
      globalActualLockingSlope D * globalActualLogScale D N := by
  rw [lockingThreshold_eq_globalActualLogScale]
  exact nat_const_add_mul_le_mul _ _ _ (globalActualLogScale_pos D N)

theorem globalActualGapEnvelope_le_slope_mul (D : CarrySeries)
    (Cgap N : ℕ) :
    globalActualGapEnvelope D Cgap N ≤
      globalActualGapSlope D Cgap * globalActualLogScale D N := by
  unfold globalActualGapEnvelope globalActualGapSlope
  have hL := globalActualLogScale_pos D N
  have hC : Cgap ≤ Cgap * globalActualLogScale D N := by
    calc
      Cgap = Cgap * 1 := by simp
      _ ≤ Cgap * globalActualLogScale D N := Nat.mul_le_mul_left Cgap hL
  calc
    D.weight.natDegree * globalActualLogScale D N + Cgap ≤
        D.weight.natDegree * globalActualLogScale D N +
          Cgap * globalActualLogScale D N := Nat.add_le_add_left hC _
    _ = (D.weight.natDegree + Cgap) *
        globalActualLogScale D N := by ring

theorem globalActualContinuationEnvelope_le_slope_mul (D : CarrySeries)
    (N : ℕ) :
    globalActualContinuationEnvelope D N ≤
      globalActualContinuationSlope D * globalActualLogScale D N := by
  let L := globalActualLogScale D N
  let a := Nat.clog D.base
    (globalActualInteriorCoalescencePolynomialConstant D + 1)
  let q := globalActualInteriorCoalescencePolynomialExponent D
  have hL : 1 ≤ L := globalActualLogScale_pos D N
  have hq : q * (L + 1) ≤ 2 * q * L := by
    calc
      q * (L + 1) = q * L + q := by ring
      _ ≤ q * L + q * L := Nat.add_le_add_left
        (by
          calc
            q = q * 1 := by simp
            _ ≤ q * L := Nat.mul_le_mul_left q hL) _
      _ = 2 * q * L := by ring
  calc
    globalActualContinuationEnvelope D N = a + q * (L + 1) := rfl
    _ ≤ a + (2 * q) * L := Nat.add_le_add_left hq a
    _ ≤ (a + 2 * q) * L := nat_const_add_mul_le_mul a (2 * q) L hL
    _ = globalActualContinuationSlope D * globalActualLogScale D N := rfl

theorem globalActualInteriorThreshold_le_slope_mul (D : CarrySeries)
    {N W m cap reserve Cgap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (hcap : cap ≤ globalActualGapEnvelope D Cgap N)
    (hm : m ≤ globalActualLogScale D N) :
    globalActualInteriorThreshold D N W m cap reserve ≤
      globalActualThresholdSlope D Cgap reserve *
        globalActualLogScale D N := by
  let L := globalActualLogScale D N
  have hthreshold := globalActualInteriorThreshold_le_envelope
    D hW hscale hcap (m := m) (reserve := reserve)
  have hstate : globalActualStatePowerExponent D N ≤
      globalActualStateSlope D * L := by
    simpa only [L] using globalActualStatePowerExponent_le_slope_mul D N
  have hgap : globalActualGapEnvelope D Cgap N ≤
      globalActualGapSlope D Cgap * L := by
    simpa only [L] using globalActualGapEnvelope_le_slope_mul D Cgap N
  have hblock : globalActualBlockScaleEnvelope D N ≤
      globalActualBlockSlope D * L := by
    simpa only [L] using globalActualBlockScaleEnvelope_le_slope_mul D N
  calc
    globalActualInteriorThreshold D N W m cap reserve ≤
        globalActualThresholdEnvelope D Cgap N m reserve := hthreshold
    _ ≤ globalActualStateSlope D * L +
        2 * (globalActualGapSlope D Cgap * L) +
        24 * (globalActualBlockSlope D * L) + reserve * L := by
      unfold globalActualThresholdEnvelope
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add hstate (Nat.mul_le_mul_left 2 hgap))
          (Nat.mul_le_mul_left 24 hblock))
        (Nat.mul_le_mul_left reserve hm)
    _ = globalActualThresholdSlope D Cgap reserve * L := by
      unfold globalActualThresholdSlope
      ring

theorem globalActualPrefixSpan_le_slope_mul (D : CarrySeries)
    {N cap Cgap : ℕ}
    (hcap : cap ≤ globalActualGapEnvelope D Cgap N) :
    lockingThreshold D N + cap + 1 ≤
      globalActualPrefixSpanSlope D Cgap * globalActualLogScale D N := by
  let L := globalActualLogScale D N
  have hlock : lockingThreshold D N ≤
      globalActualLockingSlope D * L := by
    simpa only [L] using lockingThreshold_le_slope_mul D N
  have hgap : cap ≤ globalActualGapSlope D Cgap * L := by
    simpa only [L] using
      hcap.trans (globalActualGapEnvelope_le_slope_mul D Cgap N)
  have hOne : 1 ≤ L := globalActualLogScale_pos D N
  calc
    lockingThreshold D N + cap + 1 ≤
        globalActualLockingSlope D * L +
          globalActualGapSlope D Cgap * L + L :=
      Nat.add_le_add (Nat.add_le_add hlock hgap) hOne
    _ = globalActualPrefixSpanSlope D Cgap * L := by
      unfold globalActualPrefixSpanSlope
      ring

theorem globalActualSelectedSpan_le_slope_mul (D : CarrySeries)
    {N W m cap reserve Cgap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (hcap : cap ≤ globalActualGapEnvelope D Cgap N)
    (hm : m ≤ globalActualLogScale D N) :
    globalActualInteriorThreshold D N W m cap reserve + cap + 1 ≤
      globalActualSelectedSpanSlope D Cgap reserve *
        globalActualLogScale D N := by
  let L := globalActualLogScale D N
  have ht : globalActualInteriorThreshold D N W m cap reserve ≤
      globalActualThresholdSlope D Cgap reserve * L := by
    simpa only [L] using globalActualInteriorThreshold_le_slope_mul
      D hW hscale hcap hm (reserve := reserve)
  have hg : cap ≤ globalActualGapSlope D Cgap * L := by
    simpa only [L] using
      hcap.trans (globalActualGapEnvelope_le_slope_mul D Cgap N)
  have hL : 1 ≤ L := globalActualLogScale_pos D N
  calc
    globalActualInteriorThreshold D N W m cap reserve + cap + 1 ≤
        globalActualThresholdSlope D Cgap reserve * L +
          globalActualGapSlope D Cgap * L + L :=
      Nat.add_le_add (Nat.add_le_add ht hg) hL
    _ = globalActualSelectedSpanSlope D Cgap reserve * L := by
      unfold globalActualSelectedSpanSlope
      ring

theorem globalActualClassificationCutoff_le_slope_mul (D : CarrySeries)
    {N W m cap reserve Cgap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (hcap : cap ≤ globalActualGapEnvelope D Cgap N)
    (hm : m ≤ globalActualLogScale D N) :
    globalActualClassificationCutoff D N W m cap reserve ≤
      globalActualClassificationSlope D Cgap reserve *
        globalActualLogScale D N := by
  let L := globalActualLogScale D N
  have hlock : lockingThreshold D N ≤
      globalActualLockingSlope D * L := by
    simpa only [L] using lockingThreshold_le_slope_mul D N
  have hgap : cap ≤ globalActualGapSlope D Cgap * L := by
    simpa only [L] using
      hcap.trans (globalActualGapEnvelope_le_slope_mul D Cgap N)
  have ht : globalActualInteriorThreshold D N W m cap reserve ≤
      globalActualThresholdSlope D Cgap reserve * L := by
    simpa only [L] using globalActualInteriorThreshold_le_slope_mul
      D hW hscale hcap hm (reserve := reserve)
  unfold globalActualClassificationCutoff
  calc
    lockingThreshold D N + 2 * cap + m +
        2 * globalActualInteriorThreshold D N W m cap reserve ≤
      globalActualLockingSlope D * L +
        2 * (globalActualGapSlope D Cgap * L) + L +
          2 * (globalActualThresholdSlope D Cgap reserve * L) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add hlock (Nat.mul_le_mul_left 2 hgap)) hm)
        (Nat.mul_le_mul_left 2 ht)
    _ = globalActualClassificationSlope D Cgap reserve * L := by
      unfold globalActualClassificationSlope
      ring

theorem globalActualInteriorAssemblyLoss_le_slope_mul (D : CarrySeries)
    {N W m cap reserve Cgap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (hcap : cap ≤ globalActualGapEnvelope D Cgap N)
    (hm : m ≤ globalActualLogScale D N) :
    globalActualInteriorAssemblyLoss D N W m cap reserve ≤
      globalActualAssemblySlope D Cgap reserve *
        globalActualLogScale D N := by
  let L := globalActualLogScale D N
  have hlock : lockingThreshold D N ≤
      globalActualLockingSlope D * L := by
    simpa only [L] using lockingThreshold_le_slope_mul D N
  have hgap : cap ≤ globalActualGapSlope D Cgap * L := by
    simpa only [L] using
      hcap.trans (globalActualGapEnvelope_le_slope_mul D Cgap N)
  have ht : globalActualInteriorThreshold D N W m cap reserve ≤
      globalActualThresholdSlope D Cgap reserve * L := by
    simpa only [L] using globalActualInteriorThreshold_le_slope_mul
      D hW hscale hcap hm (reserve := reserve)
  have hs : Nat.log 2
        (globalActualInteriorStateDenominatorCap D N W cap) ≤
      globalActualStateSlope D * L := by
    simpa only [L] using
      (globalActualInteriorStateLog_le_powerExponent D hW hscale).trans
        (globalActualStatePowerExponent_le_slope_mul D N)
  unfold globalActualInteriorAssemblyLoss
  calc
    lockingThreshold D N + 4 * cap + m +
        globalActualInteriorThreshold D N W m cap reserve +
          Nat.log 2 (globalActualInteriorStateDenominatorCap D N W cap) ≤
      globalActualLockingSlope D * L +
        4 * (globalActualGapSlope D Cgap * L) + L +
          globalActualThresholdSlope D Cgap reserve * L +
            globalActualStateSlope D * L := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add hlock (Nat.mul_le_mul_left 4 hgap)) hm) ht) hs
    _ = globalActualAssemblySlope D Cgap reserve * L := by
      unfold globalActualAssemblySlope
      ring

theorem globalActualTerminalLoss_le_slope_mul (D : CarrySeries)
    {N W cap : ℕ} (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N) :
    globalActualInteriorContinuationSpan D N +
        4 * globalActualInteriorBlockScaleCap D N W cap ≤
      globalActualTerminalSlope D * globalActualLogScale D N := by
  let L := globalActualLogScale D N
  have hF : globalActualInteriorContinuationSpan D N ≤
      globalActualContinuationSlope D * L := by
    simpa only [L] using
      (globalActualInteriorContinuationSpan_le_envelope D N).trans
        (globalActualContinuationEnvelope_le_slope_mul D N)
  have hblock : globalActualInteriorBlockScaleCap D N W cap ≤
      globalActualBlockSlope D * L := by
    simpa only [L] using
      (globalActualInteriorBlockScaleCap_le_envelope D hW hscale).trans
        (globalActualBlockScaleEnvelope_le_slope_mul D N)
  calc
    globalActualInteriorContinuationSpan D N +
        4 * globalActualInteriorBlockScaleCap D N W cap ≤
      globalActualContinuationSlope D * L +
        4 * (globalActualBlockSlope D * L) :=
      Nat.add_le_add hF (Nat.mul_le_mul_left 4 hblock)
    _ = globalActualTerminalSlope D * L := by
      unfold globalActualTerminalSlope
      ring

/-! ## Absorption by polynomial windows -/

theorem globalActualLogScale_cast_le_five_log (D : CarrySeries)
    {N : ℕ} (hN : 3 ≤ N) :
    (globalActualLogScale D N : ℝ) ≤ 5 * Real.log (N : ℝ) := by
  let X : ℕ := 3 * N + 1
  have hXpos : (0 : ℝ) < X := by positivity
  have hNX : X ≤ 4 * N := by dsimp only [X]; omega
  have hbaseNat : Nat.log D.base X ≤ Nat.log 2 X :=
    Nat.log_anti_left (by decide : 1 < 2) D.base_ge_two
  have hbaseReal : (Nat.log D.base X : ℝ) ≤ Nat.log 2 X := by
    exact_mod_cast hbaseNat
  have hnatReal : (Nat.log 2 X : ℝ) ≤ Real.logb 2 (X : ℝ) := by
    convert Real.natLog_le_logb X 2 using 1
    norm_num
  have hlogbMono : Real.logb 2 (X : ℝ) ≤
      Real.logb 2 (4 * (N : ℝ)) := by
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hXpos
    exact_mod_cast hNX
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 :=
    lt_of_lt_of_le (by norm_num) hlog2
  have hident : Real.logb 2 (4 * (N : ℝ)) =
      2 + Real.log (N : ℝ) / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hNpos.ne']
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    field_simp
  have hdiv : Real.log (N : ℝ) / Real.log 2 ≤
      2 * Real.log (N : ℝ) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [mul_nonneg (Real.log_natCast_nonneg N)
      (sub_nonneg.mpr hlog2)]
  unfold globalActualLogScale
  rw [Nat.cast_add, Nat.cast_one]
  change (Nat.log D.base X : ℝ) + 1 ≤ 5 * Real.log (N : ℝ)
  calc
    (Nat.log D.base X : ℝ) + 1 ≤ Real.logb 2 (X : ℝ) + 1 := by
      linarith [hbaseReal.trans hnatReal]
    _ ≤ Real.logb 2 (4 * (N : ℝ)) + 1 := by linarith
    _ = 3 + Real.log (N : ℝ) / Real.log 2 := by rw [hident]; ring
    _ ≤ 3 + 2 * Real.log (N : ℝ) := by linarith
    _ ≤ 5 * Real.log (N : ℝ) := by linarith

/-- Every fixed power of the common logarithmic scale is eventually absorbed
by an arbitrarily small positive power of `N`. -/
theorem eventually_globalActualLogScale_power_le_rpow
    (D : CarrySeries) (C : ℝ) (q : ℕ) (β : ℝ)
    (hC : 0 < C) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop,
      C * (globalActualLogScale D N : ℝ) ^ q ≤ Real.rpow N β := by
  let K : ℝ := C * 5 ^ q
  have hK : 0 < K := by dsimp only [K]; positivity
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (q : ℝ) hβ).bound
      (show 0 < (1 : ℝ) / K by positivity)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 3] with N hsmall hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hsmall' : Real.log (N : ℝ) ^ q ≤
      (1 / K) * Real.rpow N β := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 (q : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le β)] at hsmall
    rw [Real.rpow_natCast] at hsmall
    exact hsmall
  have hL := globalActualLogScale_cast_le_five_log D hN
  have hLpow : (globalActualLogScale D N : ℝ) ^ q ≤
      5 ^ q * Real.log (N : ℝ) ^ q := by
    calc
      (globalActualLogScale D N : ℝ) ^ q ≤
          (5 * Real.log (N : ℝ)) ^ q := by gcongr
      _ = 5 ^ q * Real.log (N : ℝ) ^ q := by rw [mul_pow]
  calc
    C * (globalActualLogScale D N : ℝ) ^ q ≤
        C * (5 ^ q * Real.log (N : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_left hLpow hC.le
    _ = K * Real.log (N : ℝ) ^ q := by dsimp only [K]; ring
    _ ≤ K * ((1 / K) * Real.rpow N β) :=
      mul_le_mul_of_nonneg_left hsmall' hK.le
    _ = Real.rpow N β := by field_simp

/-- A polynomial logarithmic loss times the canonical small entropy factor is
eventually bounded by `N^β`.  The fixed fraction `1/20` leaves ample room for
the logarithmic polynomial. -/
theorem eventually_globalActualLogScale_entropy_le_rpow
    (D : CarrySeries) (C : ℝ) (q : ℕ) (β : ℝ)
    (hC : 0 < C) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop,
      C * (globalActualLogScale D N : ℝ) ^ q *
          Real.rpow 2 ((β / 20) * globalActualLogScale D N) ≤
        Real.rpow N β := by
  have hpoly := eventually_globalActualLogScale_power_le_rpow
    D C q (3 * β / 4) hC (by positivity)
  filter_upwards [hpoly, eventually_ge_atTop 3] with N hpolyN hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hL := globalActualLogScale_cast_le_five_log D hN
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have hcoef : (β / 20) * Real.log 2 ≤ β / 20 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlog2le (by positivity : 0 ≤ β / 20)
  have hexponent : Real.log 2 *
        ((β / 20) * (globalActualLogScale D N : ℝ)) ≤
      Real.log (N : ℝ) * (β / 4) := by
    calc
      Real.log 2 * ((β / 20) * (globalActualLogScale D N : ℝ)) =
          (β / 20) * Real.log 2 * (globalActualLogScale D N : ℝ) := by ring
      _ ≤ (β / 20) * (globalActualLogScale D N : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ (β / 20) * (5 * Real.log (N : ℝ)) := by
        gcongr
      _ = Real.log (N : ℝ) * (β / 4) := by ring
  have hexp : Real.rpow 2
        ((β / 20) * globalActualLogScale D N) ≤
      Real.rpow N (β / 4) := by
    change (2 : ℝ) ^ ((β / 20) * (globalActualLogScale D N : ℝ)) ≤
      (N : ℝ) ^ (β / 4)
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hNpos]
    exact Real.exp_le_exp.mpr hexponent
  calc
    C * (globalActualLogScale D N : ℝ) ^ q *
        Real.rpow 2 ((β / 20) * globalActualLogScale D N) ≤
      Real.rpow N (3 * β / 4) * Real.rpow N (β / 4) :=
        mul_le_mul hpolyN hexp (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg hNpos.le _)
    _ = Real.rpow N β := by
      change (N : ℝ) ^ (3 * β / 4) * (N : ℝ) ^ (β / 4) =
        (N : ℝ) ^ β
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

theorem globalActualLogScale_tendsto_atTop (D : CarrySeries) :
    Tendsto (globalActualLogScale D) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  filter_upwards [eventually_ge_atTop (D.base ^ K)] with N hN
  have hbase : 1 < D.base :=
    lt_of_lt_of_le (by decide : 1 < 2) D.base_ge_two
  have hpowLt : D.base ^ K <
      D.base ^ globalActualLogScale D N :=
    hN.trans_lt (self_lt_base_pow_globalActualLogScale D N)
  exact (Nat.pow_lt_pow_iff_right hbase).mp hpowLt |>.le

theorem canonicalGapEnvelope_ge_logScale (D : CarrySeries)
    (Cgap N : ℕ) (hd : 0 < D.weight.natDegree) :
    globalActualLogScale D N ≤ globalActualGapEnvelope D Cgap N := by
  unfold globalActualGapEnvelope
  have hmul : globalActualLogScale D N ≤
      D.weight.natDegree * globalActualLogScale D N := by
    calc
      globalActualLogScale D N = 1 * globalActualLogScale D N := by simp
      _ ≤ D.weight.natDegree * globalActualLogScale D N :=
        Nat.mul_le_mul_right _ hd
  exact hmul.trans (Nat.le_add_right _ _)

/-- The complete realized-prefix census has an arbitrarily small power bound
when the canonical multiplicity divisor is chosen with sufficiently small
entropy. -/
theorem eventually_globalActualPrefixWordCensus_le_rpow
    (D : CarrySeries) (Cgap K : ℕ) (β : ℝ)
    (hd : 0 < D.weight.natDegree) (hK : 4 ≤ K) (hβ : 0 < β)
    (hentropy : (globalActualPrefixSpanSlope D Cgap : ℝ) *
      Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ β / 20) :
    ∀ᶠ N : ℕ in atTop,
      (globalActualPrefixWordCensus D N
          (globalActualMultiplicity D K N)
          (globalActualGapEnvelope D Cgap N) : ℝ) ≤
        Real.rpow N β := by
  let C := globalActualPrefixSpanSlope D Cgap
  have hCpos : 0 < C := by unfold C globalActualPrefixSpanSlope; omega
  have habsorb := eventually_globalActualLogScale_entropy_le_rpow
    D ((C : ℝ) ^ 2) 2 β (by positivity) hβ
  have hlarge : ∀ᶠ N : ℕ in atTop,
      K ≤ globalActualLogScale D N :=
    (globalActualLogScale_tendsto_atTop D).eventually_ge_atTop K
  filter_upwards [habsorb, hlarge] with N habsorbN hKL
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  let cap := globalActualGapEnvelope D Cgap N
  let H := lockingThreshold D N + cap
  have hlower : L ≤ H + 1 := by
    dsimp only [H, cap, L]
    exact (canonicalGapEnvelope_ge_logScale D Cgap N hd).trans
      (by omega)
  have hupper : H + 1 ≤ C * L := by
    dsimp only [H, cap, C, L]
    exact globalActualPrefixSpan_le_slope_mul D (le_refl _)
  have hfinite := boundedPositiveGapWords_card_le_logScale_entropy
    D hK hKL hlower hupper hentropy
  change (globalActualPrefixWordCensus D N m cap : ℝ) ≤
      Real.rpow N β
  unfold globalActualPrefixWordCensus
  calc
    ((boundedPositiveGapWords H m).card : ℝ) ≤
        (((C * L : ℕ) : ℝ) ^ 2) *
          Real.rpow 2 ((β / 20) * L) := by
      simpa only [H, m, C, L] using hfinite
    _ = ((C : ℝ) ^ 2) * (L : ℝ) ^ 2 *
        Real.rpow 2 ((β / 20) * L) := by
      push_cast
      ring
    _ ≤ Real.rpow N β := habsorbN

/-- Uniform small-power bound for the selected exterior continuation words. -/
theorem eventually_globalActualSelectedExteriorCensus_le_rpow
    (D : CarrySeries) (Cgap reserve K : ℕ) (β : ℝ)
    (hd : 0 < D.weight.natDegree) (hK : 4 ≤ K) (hβ : 0 < β)
    (hentropy : (globalActualSelectedSpanSlope D Cgap reserve : ℝ) *
      Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ β / 20) :
    ∀ᶠ N : ℕ in atTop, ∀ W : ℕ,
      W ≤ N →
      lockingThreshold D N + globalActualGapEnvelope D Cgap N ≤ N →
      (globalActualSelectedExteriorCensus
          (globalActualInteriorThreshold D N W
            (globalActualMultiplicity D K N)
            (globalActualGapEnvelope D Cgap N) reserve)
          (globalActualMultiplicity D K N)
          (globalActualGapEnvelope D Cgap N) : ℝ) ≤ Real.rpow N β := by
  let C := globalActualSelectedSpanSlope D Cgap reserve
  have hCpos : 0 < C := by unfold C globalActualSelectedSpanSlope; omega
  have habsorb := eventually_globalActualLogScale_entropy_le_rpow
    D ((C : ℝ) ^ 2) 2 β (by positivity) hβ
  have hlarge : ∀ᶠ N : ℕ in atTop,
      K ≤ globalActualLogScale D N :=
    (globalActualLogScale_tendsto_atTop D).eventually_ge_atTop K
  filter_upwards [habsorb, hlarge] with N habsorbN hKL
  intro W hW hscale
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  let cap := globalActualGapEnvelope D Cgap N
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  let H := threshold + cap
  have hm : m ≤ L := by
    dsimp only [m, globalActualMultiplicity, L]
    exact Nat.div_le_self _ _
  have hlower : L ≤ H + 1 := by
    dsimp only [H, cap, L]
    exact (canonicalGapEnvelope_ge_logScale D Cgap N hd).trans
      (by omega)
  have hupper : H + 1 ≤ C * L := by
    dsimp only [H, threshold, cap, C, L]
    exact globalActualSelectedSpan_le_slope_mul D hW hscale
      (le_refl _) hm
  have hfinite := boundedPositiveGapWords_card_le_logScale_entropy
    D hK hKL hlower hupper hentropy
  change (globalActualSelectedExteriorCensus threshold m cap : ℝ) ≤
      Real.rpow N β
  unfold globalActualSelectedExteriorCensus
  calc
    ((boundedPositiveGapWords H m).card : ℝ) ≤
        (((C * L : ℕ) : ℝ) ^ 2) *
          Real.rpow 2 ((β / 20) * L) := by
      simpa only [H, m, C, L] using hfinite
    _ = ((C : ℝ) ^ 2) * (L : ℝ) ^ 2 *
        Real.rpow 2 ((β / 20) * L) := by
      push_cast
      ring
    _ ≤ Real.rpow N β := habsorbN

/-- Uniform small-power bound for the pre-exterior binary record census. -/
theorem eventually_globalActualPreExteriorCensus_le_rpow
    (D : CarrySeries) (Cgap K : ℕ) (β : ℝ)
    (hKpos : 0 < K) (hβ : 0 < β)
    (hbranch : 1 / (K : ℝ) ≤ β / 20) :
    ∀ᶠ N : ℕ in atTop,
      (globalActualPreExteriorCensus
          (globalActualMultiplicity D K N)
          (globalActualGapEnvelope D Cgap N) : ℝ) ≤
        Real.rpow N β := by
  let C : ℝ := 2 * (globalActualGapSlope D Cgap + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have habsorb := eventually_globalActualLogScale_entropy_le_rpow
    D C 2 β hC hβ
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 1 K ≤ globalActualLogScale D N :=
    (globalActualLogScale_tendsto_atTop D).eventually_ge_atTop (max 1 K)
  filter_upwards [habsorb, hlarge] with N habsorbN hlargeN
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  let cap := globalActualGapEnvelope D Cgap N
  have hL : 1 ≤ L := (le_max_left _ _).trans hlargeN
  have hKL : K ≤ L := (le_max_right _ _).trans hlargeN
  have hmCast : (m : ℝ) ≤ (L : ℝ) / K := by
    dsimp only [m, globalActualMultiplicity]
    exact Nat.cast_div_le
  have hmExp : (m : ℝ) ≤ (β / 20) * L := by
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    calc
      (m : ℝ) ≤ (L : ℝ) / K := hmCast
      _ = (1 / (K : ℝ)) * L := by field_simp
      _ ≤ (β / 20) * L := mul_le_mul_of_nonneg_right hbranch hL0
  have hpow : ((2 ^ m : ℕ) : ℝ) ≤
      Real.rpow 2 ((β / 20) * L) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hmExp
  have hmNat : m ≤ L := by
    exact Nat.div_le_self _ _
  have hmOne : (m + 1 : ℕ) ≤ 2 * L := by omega
  have hcapNat : cap ≤ globalActualGapSlope D Cgap * L := by
    dsimp only [cap, L]
    exact globalActualGapEnvelope_le_slope_mul D Cgap N
  have hcapOne : 1 + cap ≤
      (globalActualGapSlope D Cgap + 1) * L := by
    calc
      1 + cap ≤ L + globalActualGapSlope D Cgap * L :=
        Nat.add_le_add hL hcapNat
      _ = (globalActualGapSlope D Cgap + 1) * L := by ring
  have hpreNat : globalActualPreExteriorCensus m cap ≤
      (2 * L) *
        ((globalActualGapSlope D Cgap + 1) * L) * 2 ^ m := by
    unfold globalActualPreExteriorCensus
    have hpOne : 1 ≤ 2 ^ m := by
      have hp : 0 < 2 ^ m := pow_pos (by decide : 0 < (2 : ℕ)) _
      omega
    have hinner : 1 + cap * 2 ^ m ≤ (1 + cap) * 2 ^ m := by
      calc
        1 + cap * 2 ^ m ≤ 2 ^ m + cap * 2 ^ m :=
          Nat.add_le_add_right hpOne _
        _ = (1 + cap) * 2 ^ m := by ring
    have hinner' : 1 + cap * 2 ^ m ≤
        ((globalActualGapSlope D Cgap + 1) * L) * 2 ^ m :=
      hinner.trans (Nat.mul_le_mul_right (2 ^ m) hcapOne)
    calc
      (m + 1) * (1 + cap * 2 ^ m) ≤
          (2 * L) *
            (((globalActualGapSlope D Cgap + 1) * L) * 2 ^ m) :=
        Nat.mul_le_mul hmOne hinner'
      _ = (2 * L) *
          ((globalActualGapSlope D Cgap + 1) * L) * 2 ^ m := by ring
  have hpre : (globalActualPreExteriorCensus m cap : ℝ) ≤
      C * (L : ℝ) ^ 2 * Real.rpow 2 ((β / 20) * L) := by
    have hpreReal : (globalActualPreExteriorCensus m cap : ℝ) ≤
        ((2 * L) * ((globalActualGapSlope D Cgap + 1) * L) * 2 ^ m : ℕ) := by
      exact_mod_cast hpreNat
    calc
      (globalActualPreExteriorCensus m cap : ℝ) ≤
          ((2 * L) * ((globalActualGapSlope D Cgap + 1) * L) * 2 ^ m : ℕ) :=
        hpreReal
      _ = C * (L : ℝ) ^ 2 * ((2 ^ m : ℕ) : ℝ) := by
        dsimp only [C]
        push_cast
        ring
      _ ≤ C * (L : ℝ) ^ 2 * Real.rpow 2 ((β / 20) * L) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  exact hpre.trans habsorbN

/-! ## Exterior fibre absorption -/

theorem globalActualInteriorStateDenominatorCap_pos (D : CarrySeries)
    {N W cap : ℕ} (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hcap : 0 < cap) :
    0 < globalActualInteriorStateDenominatorCap D N W cap := by
  unfold globalActualInteriorStateDenominatorCap
  have hsum : 0 < W + lockingThreshold D N + cap := by omega
  have hp : 0 < (W + lockingThreshold D N + cap) ^
      vandermondeExponent D.weight.natDegree :=
    pow_pos hsum _
  exact Nat.mul_pos
    (Nat.mul_pos hp D.denominator_pos)
    (Int.natAbs_pos.mpr hw.ne')

/-- Once the carry-height factor is paid by the remaining `2*cap` digits, the
whole exterior polynomial-sublevel fibre factor is at most `3d`. -/
theorem globalActualExteriorFibreEnvelope_le_three_mul_degree
    (D : CarrySeries) {N W m cap reserve : ℕ}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hcap : 0 < cap)
    (hheight :
      D.heightNatConstant * (N + W + m * cap + 1) ^
          D.weight.natDegree * (D.base - 1) ≤
        D.base ^ (2 * cap - 1)) :
    globalActualExteriorFibreEnvelope D N W m cap
        (globalActualInteriorThreshold D N W m cap reserve) ≤
      3 * D.weight.natDegree := by
  let Qcap := globalActualInteriorStateDenominatorCap D N W cap
  let z := Nat.log 2 Qcap
  let threshold := globalActualInteriorThreshold D N W m cap reserve
  have hQpos : 0 < Qcap := by
    dsimp only [Qcap]
    exact globalActualInteriorStateDenominatorCap_pos D hw hcap
  have hQpow : Qcap ≤ 2 ^ (z + 1) := by
    exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) Qcap).le
  have hbase : 1 < D.base :=
    lt_of_lt_of_le (by decide : 1 < 2) D.base_ge_two
  have htwoBase : 2 ^ (z + 1) ≤ D.base ^ (z + 1) :=
    Nat.pow_le_pow_left D.base_ge_two (z + 1)
  have hthreshold : z + 2 * cap ≤ threshold := by
    dsimp only [z, threshold, Qcap]
    unfold globalActualInteriorThreshold
    omega
  have hsplit : z + 1 + (2 * cap - 1) = z + 2 * cap := by omega
  have hdenNat : Qcap * D.base ^ (2 * cap - 1) ≤
      D.base ^ threshold := by
    calc
      Qcap * D.base ^ (2 * cap - 1) ≤
          D.base ^ (z + 1) * D.base ^ (2 * cap - 1) :=
        Nat.mul_le_mul_right _ (hQpow.trans htwoBase)
      _ = D.base ^ (z + 2 * cap) := by rw [← pow_add, hsplit]
      _ ≤ D.base ^ threshold :=
        Nat.pow_le_pow_right (by omega) hthreshold
  have hnumNat :
      D.heightNatConstant * (N + W + m * cap + 1) ^
            D.weight.natDegree * Qcap * (D.base - 1) ≤
        D.base ^ threshold := by
    calc
      D.heightNatConstant * (N + W + m * cap + 1) ^
            D.weight.natDegree * Qcap * (D.base - 1) =
          Qcap * (D.heightNatConstant *
            (N + W + m * cap + 1) ^ D.weight.natDegree *
              (D.base - 1)) := by ring
      _ ≤ Qcap * D.base ^ (2 * cap - 1) :=
        Nat.mul_le_mul_left Qcap hheight
      _ ≤ D.base ^ threshold := hdenNat
  have hdenPos : (0 : ℝ) < (D.base : ℝ) ^ threshold := by
    positivity
  have hbaseCastSub : (((D.base - 1 : ℕ) : ℝ)) = (D.base : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ D.base from
      (show 1 ≤ 2 by decide).trans D.base_ge_two)]
    norm_num
  have hratio :
      (((D.heightNatConstant * (N + W + m * cap + 1) ^
            D.weight.natDegree : ℕ) : ℝ) * (Qcap : ℝ) *
          (D.base - 1 : ℝ) /
        (D.base : ℝ) ^ threshold) ≤ 1 := by
    rw [div_le_one hdenPos]
    rw [← hbaseCastSub]
    exact_mod_cast hnumNat
  have hbaseSub : (0 : ℝ) ≤ D.base - 1 := by
    have : (1 : ℝ) ≤ D.base := by
      exact_mod_cast (show 1 ≤ D.base from
        (by exact (show 1 ≤ 2 by decide).trans D.base_ge_two))
    linarith
  have hratio0 : 0 ≤
      (((D.heightNatConstant * (N + W + m * cap + 1) ^
            D.weight.natDegree : ℕ) : ℝ) * (Qcap : ℝ) *
          (D.base - 1 : ℝ) /
        (D.base : ℝ) ^ threshold) := by positivity
  have hpow :
      (((D.heightNatConstant * (N + W + m * cap + 1) ^
            D.weight.natDegree : ℕ) : ℝ) * (Qcap : ℝ) *
          (D.base - 1 : ℝ) /
        (D.base : ℝ) ^ threshold) ^
          (((D.weight.natDegree : ℝ))⁻¹) ≤ 1 :=
    Real.rpow_le_one hratio0 hratio (by positivity)
  unfold globalActualExteriorFibreEnvelope
  dsimp only [Qcap, threshold] at hpow ⊢
  have hpow' :
      (((D.heightNatConstant : ℝ) *
              ((N : ℝ) + W + m * cap + 1) ^ D.weight.natDegree) *
            (globalActualInteriorStateDenominatorCap D N W cap : ℝ) *
            ((D.base : ℝ) - 1) /
          (D.base : ℝ) ^
            globalActualInteriorThreshold D N W m cap reserve) ^
              (((D.weight.natDegree : ℝ))⁻¹) ≤ 1 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using hpow
  push_cast
  have hscaled :
      (2 * (D.weight.natDegree : ℝ)) *
          (((D.heightNatConstant : ℝ) *
                ((N : ℝ) + W + m * cap + 1) ^ D.weight.natDegree) *
              (globalActualInteriorStateDenominatorCap D N W cap : ℝ) *
              ((D.base : ℝ) - 1) /
            (D.base : ℝ) ^
              globalActualInteriorThreshold D N W m cap reserve) ^
                (((D.weight.natDegree : ℝ))⁻¹) ≤
        (2 * (D.weight.natDegree : ℝ)) * 1 :=
    mul_le_mul_of_nonneg_left hpow' (by positivity)
  calc
    (D.weight.natDegree : ℝ) + 2 * D.weight.natDegree *
        (((D.heightNatConstant : ℝ) *
              ((N : ℝ) + W + m * cap + 1) ^ D.weight.natDegree) *
            (globalActualInteriorStateDenominatorCap D N W cap : ℝ) *
            ((D.base : ℝ) - 1) /
          (D.base : ℝ) ^
            globalActualInteriorThreshold D N W m cap reserve) ^
              (((D.weight.natDegree : ℝ))⁻¹) ≤
      (D.weight.natDegree : ℝ) + 2 * D.weight.natDegree * 1 := by
        simpa only [add_comm] using
          add_le_add_left hscaled (D.weight.natDegree : ℝ)
    _ = 3 * D.weight.natDegree := by ring

/-- For the canonical logarithmic multiplicity and gap envelope, the natural
carry-height payment required by the preceding fibre lemma holds eventually,
uniformly for `W ≤ N`. -/
theorem eventually_globalActualExteriorHeight_paid (D : CarrySeries)
    (Cgap K : ℕ) (hd : 0 < D.weight.natDegree) (_hKpos : 0 < K) :
    ∀ᶠ N : ℕ in atTop, ∀ W : ℕ, W ≤ N →
      D.heightNatConstant *
          (N + W + globalActualMultiplicity D K N *
              globalActualGapEnvelope D Cgap N + 1) ^
            D.weight.natDegree * (D.base - 1) ≤
        D.base ^ (2 * globalActualGapEnvelope D Cgap N - 1) := by
  let d := D.weight.natDegree
  let C : ℕ := D.heightNatConstant * 4 ^ d * (D.base - 1)
  have hlargeLog : ∀ᶠ N : ℕ in atTop,
      max 1 (Nat.clog D.base C + 1) ≤ globalActualLogScale D N :=
    (globalActualLogScale_tendsto_atTop D).eventually_ge_atTop
      (max 1 (Nat.clog D.base C + 1))
  have hmcapSmallReal := eventually_globalActualLogScale_power_le_rpow
    D (globalActualGapSlope D Cgap : ℝ) 2 1
      (by unfold globalActualGapSlope; positivity) (by norm_num)
  filter_upwards [hlargeLog, hmcapSmallReal, eventually_ge_atTop 1] with
      N hlarge hpoly hN
  intro W hW
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  let cap := globalActualGapEnvelope D Cgap N
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hclog : Nat.clog D.base C + 1 ≤ L :=
    (le_max_right _ _).trans hlarge
  have hm : m ≤ L := by
    dsimp only [m, globalActualMultiplicity, L]
    exact Nat.div_le_self _ _
  have hcap : cap ≤ globalActualGapSlope D Cgap * L := by
    dsimp only [cap, L]
    exact globalActualGapEnvelope_le_slope_mul D Cgap N
  have hmcap : m * cap ≤
      globalActualGapSlope D Cgap * L ^ 2 := by
    calc
      m * cap ≤ L * (globalActualGapSlope D Cgap * L) :=
        Nat.mul_le_mul hm hcap
      _ = globalActualGapSlope D Cgap * L ^ 2 := by ring
  have hpolyNat : globalActualGapSlope D Cgap * L ^ 2 ≤ N := by
    have hpoly' :
        ((globalActualGapSlope D Cgap * L ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      have hpolyR := hpoly
      change (globalActualGapSlope D Cgap : ℝ) *
          (globalActualLogScale D N : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 : ℝ) at hpolyR
      rw [Real.rpow_one] at hpolyR
      simpa only [L] using hpolyR
    exact_mod_cast hpoly'
  have hsum : N + W + m * cap + 1 ≤ 4 * N := by
    have hmN := hmcap.trans hpolyNat
    omega
  have hNpow : N ^ d ≤ D.base ^ (L * d) := by
    calc
      N ^ d ≤ (D.base ^ L) ^ d :=
        Nat.pow_le_pow_left
          (self_lt_base_pow_globalActualLogScale D N).le d
      _ = D.base ^ (L * d) := by rw [Nat.pow_mul]
  have hCpow : C ≤ D.base ^ (d * L - 1) := by
    have hCbase : C ≤ D.base ^ Nat.clog D.base C :=
      Nat.le_pow_clog
        (lt_of_lt_of_le (by decide : 1 < 2) D.base_ge_two) C
    have hexp : Nat.clog D.base C ≤ d * L - 1 := by
      have hdL : L ≤ d * L := by
        calc L = 1 * L := by simp
             _ ≤ d * L := Nat.mul_le_mul_right L hd
      omega
    exact hCbase.trans (Nat.pow_le_pow_right
      (lt_of_lt_of_le (by decide : 0 < 2) D.base_ge_two) hexp)
  have hraw : D.heightNatConstant * (4 * N) ^ d * (D.base - 1) ≤
      D.base ^ (2 * d * L - 1) := by
    calc
      D.heightNatConstant * (4 * N) ^ d * (D.base - 1) =
          C * N ^ d := by
        dsimp only [C, d]
        rw [Nat.mul_pow]
        ring
      _ ≤ D.base ^ (d * L - 1) * D.base ^ (L * d) :=
        Nat.mul_le_mul hCpow hNpow
      _ = D.base ^ ((d * L - 1) + L * d) := by rw [pow_add]
      _ = D.base ^ (2 * d * L - 1) := by
        congr 1
        have hdLpos : 0 < d * L := Nat.mul_pos hd hL
        rw [Nat.mul_comm L d]
        simp only [mul_assoc]
        omega
  have hexpCap : 2 * d * L - 1 ≤ 2 * cap - 1 := by
    have hcapd : d * L ≤ cap := by
      dsimp only [cap, globalActualGapEnvelope, L]
      exact Nat.le_add_right _ _
    simpa only [mul_assoc] using
      Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hcapd) 1
  calc
    D.heightNatConstant * (N + W + m * cap + 1) ^ d *
        (D.base - 1) ≤
      D.heightNatConstant * (4 * N) ^ d * (D.base - 1) := by gcongr
    _ ≤ D.base ^ (2 * d * L - 1) := hraw
    _ ≤ D.base ^ (2 * cap - 1) :=
      Nat.pow_le_pow_right
        (lt_of_lt_of_le (by decide : 0 < 2) D.base_ge_two) hexpCap

/-! ## Final absorption bookkeeping -/

/-- Window geometry is monotone in the advertised gap cap. -/
theorem WindowGeometry.mono_cap {S : Set ℕ} {e : SupportEnumeration S}
    {N W m G G' : ℕ}
    (h : WindowGeometry e N W m G) (hGG' : G ≤ G') :
    WindowGeometry e N W m G' := by
  refine ⟨?_, ?_⟩
  · exact h.first_le.trans (Nat.add_le_add_left hGG' N)
  · intro q hq
    exact (h.gaps_le q hq).trans hGG'

/-- Explicit logarithmic gap bound from any fixed natural coefficient
dominating the carry-height envelope.  Unlike the existential compatibility
theorem in `Carry`, the displayed additive constant is suitable for uniform
quantifier order. -/
theorem CarrySeries.eventual_gap_log_bound_of_coefficient
    (D : CarrySeries) (C : ℕ) (_hCpos : 0 < C)
    (hCheight : D.heightConstant * (2 : ℝ) ^ D.weight.natDegree ≤ C) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g →
        g ≤ D.weight.natDegree * Nat.log D.base x +
          (Nat.clog D.base C + D.weight.natDegree + 1) := by
  obtain ⟨xanchor, hanchor⟩ := D.eventually_gap_lt_anchor
  refine ⟨max xanchor D.positiveFrom, ?_⟩
  intro x hx g hgap
  have hxanchor : xanchor ≤ x := (le_max_left _ _).trans hx
  have hxcut : D.positiveFrom ≤ x := (le_max_right _ _).trans hx
  have hgltx : g < x := hanchor x hxanchor g hgap
  have hpower := D.gap_power_bound hxcut hgap
  have hsumNat : x + g ≤ 2 * x := by omega
  have hsumReal : (x + g : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hsumNat
  have hpoly :
      D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree ≤
        (C : ℝ) * (x : ℝ) ^ D.weight.natDegree := by
    calc
      D.heightConstant * (x + g : ℝ) ^ D.weight.natDegree ≤
          D.heightConstant * (2 * (x : ℝ)) ^ D.weight.natDegree := by
        gcongr
        exact D.heightConstant_pos.le
      _ = (D.heightConstant * (2 : ℝ) ^ D.weight.natDegree) *
          (x : ℝ) ^ D.weight.natDegree := by
        rw [mul_pow]
        ring
      _ ≤ (C : ℝ) * (x : ℝ) ^ D.weight.natDegree := by gcongr
  have hnatural :
      D.base ^ (g - 1) ≤ C * x ^ D.weight.natDegree := by
    exact_mod_cast hpower.trans hpoly
  have hbNat : 1 < D.base :=
    lt_of_lt_of_le (by omega) D.base_ge_two
  have hCpow : C ≤ D.base ^ Nat.clog D.base C :=
    Nat.le_pow_clog hbNat C
  have hxpow : x < D.base ^ (Nat.log D.base x + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hbNat x
  have hxpowLe : x ^ D.weight.natDegree ≤
      (D.base ^ (Nat.log D.base x + 1)) ^ D.weight.natDegree :=
    Nat.pow_le_pow_left hxpow.le _
  have hproduct : C * x ^ D.weight.natDegree ≤
      D.base ^ Nat.clog D.base C *
        (D.base ^ (Nat.log D.base x + 1)) ^ D.weight.natDegree :=
    Nat.mul_le_mul hCpow hxpowLe
  have hpowers : D.base ^ (g - 1) ≤
      D.base ^ (Nat.clog D.base C +
        D.weight.natDegree * (Nat.log D.base x + 1)) := by
    calc
      D.base ^ (g - 1) ≤ C * x ^ D.weight.natDegree := hnatural
      _ ≤ D.base ^ Nat.clog D.base C *
          (D.base ^ (Nat.log D.base x + 1)) ^ D.weight.natDegree := hproduct
      _ = D.base ^ (Nat.clog D.base C +
          D.weight.natDegree * (Nat.log D.base x + 1)) := by
        rw [← pow_mul, ← pow_add]
        simp only [Nat.mul_comm]
  have hexponent : g - 1 ≤ Nat.clog D.base C +
      D.weight.natDegree * (Nat.log D.base x + 1) :=
    (Nat.pow_le_pow_iff_right hbNat).mp hpowers
  have hgpos : 0 < g := hgap.1
  calc
    g = (g - 1) + 1 := by omega
    _ ≤ (Nat.clog D.base C +
          D.weight.natDegree * (Nat.log D.base x + 1)) + 1 :=
      Nat.add_le_add_right hexponent 1
    _ = D.weight.natDegree * Nat.log D.base x +
        (Nat.clog D.base C + D.weight.natDegree + 1) := by ring

/-- A supplied eventual gap bound gives window geometry as soon as all touched
endpoints lie below a common cap. -/
theorem CarrySeries.windowGeometry_of_gap_bound_endpoint_cap
    (D : CarrySeries) {Cgap xgap N W m B : ℕ}
    (hgap : ∀ x : ℕ, xgap ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g →
        g ≤ D.weight.natDegree * Nat.log D.base x + Cgap)
    (hN : D.positiveEnumeration.a
      (Erdos260.firstIndexAbove D.positiveEnumeration xgap) ≤ N)
    (hNB : N ≤ B)
    (hcap : D.positiveEnumeration.a
      (afterWindowIndex D.positiveEnumeration N W + m) ≤ B) :
    WindowGeometry D.positiveEnumeration N W m
      (D.weight.natDegree * Nat.log D.base B + Cgap) := by
  let e := D.positiveEnumeration
  let k₀ := Erdos260.firstIndexAbove e xgap
  let i := firstWindowIndex e N
  let j := afterWindowIndex e N W
  have hk₀i : k₀ < i := by
    by_contra hnot
    have hik₀ : i ≤ k₀ := Nat.le_of_not_gt hnot
    have hmono : e.a i ≤ e.a k₀ := e.strictMono.monotone hik₀
    have hiSpec : N < e.a i := by
      dsimp [i, firstWindowIndex]
      exact Erdos260.firstIndexAbove_spec e N
    have hN' : e.a k₀ ≤ N := by simpa only [e, k₀] using hN
    omega
  have hiPos : 0 < i := lt_of_le_of_lt (Nat.zero_le k₀) hk₀i
  let p := i - 1
  have hpSucc : p + 1 = i := by dsimp [p]; omega
  have hk₀p : k₀ ≤ p := by dsimp [p]; omega
  have hpI : p < i := by dsimp [p]; omega
  have hpUpper : e.a p ≤ N := by
    dsimp [i, firstWindowIndex] at hpI
    exact Erdos260.firstIndexAbove_minimal e N p hpI
  have hpGapStart : xgap ≤ e.a p := by
    have hk₀Spec : xgap < e.a k₀ := by
      dsimp [k₀]
      exact Erdos260.firstIndexAbove_spec e xgap
    have hmono := e.strictMono.monotone hk₀p
    omega
  let G := D.weight.natDegree * Nat.log D.base B + Cgap
  have hpGap : Erdos260.supportGap e p ≤ G := by
    have hraw := hgap (e.a p) hpGapStart
      (Erdos260.supportGap e p)
      (D.positiveEnumeration_gap_isSupportGap p)
    have hlog : Nat.log D.base (e.a p) ≤ Nat.log D.base B := by
      apply Nat.log_mono_right
      exact hpUpper.trans hNB
    have hmul := Nat.mul_le_mul_left D.weight.natDegree hlog
    exact hraw.trans (Nat.add_le_add_right hmul Cgap)
  refine ⟨?_, ?_⟩
  · change e.a i ≤ N + G
    have hpMono : e.a p ≤ e.a i := e.strictMono.monotone hpI.le
    have hgapEq : Erdos260.supportGap e p = e.a i - e.a p := by
      simp only [Erdos260.supportGap, hpSucc]
    rw [hgapEq] at hpGap
    omega
  · intro q hq
    have hq' := Finset.mem_Ico.mp hq
    have hiSpec : N < e.a i := by
      dsimp [i, firstWindowIndex]
      exact Erdos260.firstIndexAbove_spec e N
    have hqStart : xgap ≤ e.a q := by
      have hiq : i ≤ q := by simpa only [i] using hq'.1
      have hmono := e.strictMono.monotone hiq
      omega
    have hqEnd : e.a q ≤ B := by
      have hqle : q ≤ j + m := by
        have hupper : q < j + m := by
          simpa only [e, j] using hq'.2
        exact hupper.le
      have hmono := e.strictMono.monotone hqle
      exact hmono.trans hcap
    have hraw := hgap (e.a q) hqStart
      (Erdos260.supportGap e q)
      (D.positiveEnumeration_gap_isSupportGap q)
    have hlog : Nat.log D.base (e.a q) ≤ Nat.log D.base B :=
      Nat.log_mono_right hqEnd
    have hmul := Nat.mul_le_mul_left D.weight.natDegree hlog
    exact hraw.trans (Nat.add_le_add_right hmul Cgap)

/-- A fixed eventual logarithmic gap bound supplies the exact window geometry
interface used by the completion proof; only its starting index depends on the
support enumeration. -/
theorem CarrySeries.exists_windowGeometry_of_gap_bound
    (D : CarrySeries) {Cgap xgap : ℕ}
    (hgap : ∀ x : ℕ, xgap ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g →
        g ≤ D.weight.natDegree * Nat.log D.base x + Cgap) :
    ∃ N₀ : ℕ, ∀ N W m : ℕ, N₀ ≤ N → W ≤ N →
      (m + 1) *
        (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) < N →
      WindowGeometry D.positiveEnumeration N W m
        (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) := by
  let N₀ := D.positiveEnumeration.a
    (Erdos260.firstIndexAbove D.positiveEnumeration xgap)
  refine ⟨N₀, ?_⟩
  intro N W m hN hW hsmall
  have hcap := D.endpoint_cap_of_gap_bound hgap
    (by simpa only [N₀] using hN) hW hsmall
  exact D.windowGeometry_of_gap_bound_endpoint_cap hgap
    (by simpa only [N₀] using hN) (by omega) hcap

/-! ### Invariance of the uniform core data -/

theorem CarrySeries.heightConstant_eq_of_core (D E : CarrySeries)
    (hbase : D.base = E.base) (hweight : D.weight = E.weight)
    (hden : D.denominator = E.denominator) :
    D.heightConstant = E.heightConstant := by
  unfold CarrySeries.heightConstant
  rw [hbase, hweight, hden]

theorem CarrySeries.heightNatConstant_eq_of_core (D E : CarrySeries)
    (hbase : D.base = E.base) (hweight : D.weight = E.weight)
    (hden : D.denominator = E.denominator) :
    D.heightNatConstant = E.heightNatConstant := by
  unfold CarrySeries.heightNatConstant
  rw [D.heightConstant_eq_of_core E hbase hweight hden]

theorem CarrySeries.gapCoefficient_eq_of_core (D E : CarrySeries)
    (hbase : D.base = E.base) (hweight : D.weight = E.weight)
    (hden : D.denominator = E.denominator) :
    D.gapCoefficient = E.gapCoefficient := by
  unfold CarrySeries.gapCoefficient
  rw [D.heightConstant_eq_of_core E hbase hweight hden, hweight]

theorem globalActualInteriorSamplingExponent_eq_of_core
    (D E : CarrySeries) (hweight : D.weight = E.weight) :
    globalActualInteriorSamplingExponent D =
      globalActualInteriorSamplingExponent E := by
  unfold globalActualInteriorSamplingExponent
  rw [hweight]

theorem globalActualInteriorEntropyExponent_eq_of_core
    (D E : CarrySeries) (hweight : D.weight = E.weight) :
    globalActualInteriorEntropyExponent D =
      globalActualInteriorEntropyExponent E := by
  unfold globalActualInteriorEntropyExponent
  rw [globalActualInteriorSamplingExponent_eq_of_core D E hweight]

theorem globalActualInteriorDecayRatio_eq_of_core
    (D E : CarrySeries) (hweight : D.weight = E.weight) :
    globalActualInteriorDecayRatio D = globalActualInteriorDecayRatio E := by
  unfold globalActualInteriorDecayRatio
  rw [globalActualInteriorEntropyExponent_eq_of_core D E hweight,
    globalActualInteriorSamplingExponent_eq_of_core D E hweight]

theorem globalActualInteriorNormalizationExponent_eq_of_core
    (D E : CarrySeries) (hweight : D.weight = E.weight)
    (hden : D.denominator = E.denominator) :
    globalActualInteriorNormalizationExponent D =
      globalActualInteriorNormalizationExponent E := by
  unfold globalActualInteriorNormalizationExponent
  rw [hweight, hden]

theorem globalActualInteriorDecayShift_eq_of_core
    (D E : CarrySeries) (hweight : D.weight = E.weight)
    (hden : D.denominator = E.denominator) :
    globalActualInteriorDecayShift D = globalActualInteriorDecayShift E := by
  unfold globalActualInteriorDecayShift
  rw [globalActualInteriorSamplingExponent_eq_of_core D E hweight,
    globalActualInteriorNormalizationExponent_eq_of_core D E hweight hden]

theorem globalActualInteriorHighTail_eq_of_core
    (D E : CarrySeries) (hweight : D.weight = E.weight)
    (hden : D.denominator = E.denominator) :
    globalActualInteriorHighTail D = globalActualInteriorHighTail E := by
  funext reserve
  unfold globalActualInteriorHighTail
  rw [hweight,
    globalActualInteriorDecayShift_eq_of_core D E hweight hden,
    globalActualInteriorDecayRatio_eq_of_core D E hweight]

theorem globalActualInteriorHighGeometricReserve_eq_of_core
    (D E : CarrySeries) (_hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator)
    (hdD : 0 < D.weight.natDegree) (hdE : 0 < E.weight.natDegree) :
    globalActualInteriorHighGeometricReserve D hdD =
      globalActualInteriorHighGeometricReserve E hdE := by
  have hentropy := globalActualInteriorEntropyExponent_eq_of_core D E hweight
  have hwords :
      retainedBlockWordsReserve
          (globalActualInteriorEntropyExponent D)
          (globalActualInteriorEntropyExponent_pos D hdD) =
        retainedBlockWordsReserve
          (globalActualInteriorEntropyExponent E)
          (globalActualInteriorEntropyExponent_pos E hdE) := by
    exact retainedBlockWordsReserve_congr _ _ hentropy
  unfold globalActualInteriorHighGeometricReserve
  rw [hwords,
    globalActualInteriorNormalizationExponent_eq_of_core D E hweight hden]

theorem globalActualStateSlope_eq_of_core
    (D E : CarrySeries) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    globalActualStateSlope D = globalActualStateSlope E := by
  unfold globalActualStateSlope
  rw [hbase, hweight, hden]

theorem globalActualBlockSlope_eq_of_core
    (D E : CarrySeries) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    globalActualBlockSlope D = globalActualBlockSlope E := by
  unfold globalActualBlockSlope
  rw [globalActualStateSlope_eq_of_core D E hbase hweight hden]

theorem lockingPolynomialConstant_eq_of_core
    (D E : CarrySeries) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    lockingPolynomialConstant D = lockingPolynomialConstant E := by
  unfold lockingPolynomialConstant
  rw [hweight, D.heightNatConstant_eq_of_core E hbase hweight hden]

theorem globalActualLockingSlope_eq_of_core
    (D E : CarrySeries) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    globalActualLockingSlope D = globalActualLockingSlope E := by
  unfold globalActualLockingSlope lockingPolynomialExponent
  rw [hbase, hweight,
    lockingPolynomialConstant_eq_of_core D E hbase hweight hden]

theorem globalActualGapSlope_eq_of_core
    (D E : CarrySeries) (Cgap : ℕ) (hweight : D.weight = E.weight) :
    globalActualGapSlope D Cgap = globalActualGapSlope E Cgap := by
  unfold globalActualGapSlope
  rw [hweight]

theorem globalActualContinuationSlope_eq_of_core
    (D E : CarrySeries) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    globalActualContinuationSlope D = globalActualContinuationSlope E := by
  unfold globalActualContinuationSlope
    globalActualInteriorCoalescencePolynomialConstant
    globalActualInteriorCoalescencePolynomialExponent
  rw [hbase, hweight, D.heightNatConstant_eq_of_core E hbase hweight hden]

theorem globalActualPrefixSpanSlope_eq_of_core
    (D E : CarrySeries) (Cgap : ℕ) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    globalActualPrefixSpanSlope D Cgap =
      globalActualPrefixSpanSlope E Cgap := by
  unfold globalActualPrefixSpanSlope
  rw [globalActualLockingSlope_eq_of_core D E hbase hweight hden,
    globalActualGapSlope_eq_of_core D E Cgap hweight]

theorem globalActualSelectedSpanSlope_eq_of_core
    (D E : CarrySeries) (Cgap reserve : ℕ) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    globalActualSelectedSpanSlope D Cgap reserve =
      globalActualSelectedSpanSlope E Cgap reserve := by
  unfold globalActualSelectedSpanSlope globalActualThresholdSlope
  rw [globalActualStateSlope_eq_of_core D E hbase hweight hden,
    globalActualGapSlope_eq_of_core D E Cgap hweight,
    globalActualBlockSlope_eq_of_core D E hbase hweight hden]

/-- The canonical quotient multiplicity is positive once the logarithmic
scale contains its divisor. -/
theorem globalActualMultiplicity_pos (D : CarrySeries) {K N : ℕ}
    (hKpos : 0 < K) (hKL : K ≤ globalActualLogScale D N) :
    0 < globalActualMultiplicity D K N := by
  unfold globalActualMultiplicity
  exact Nat.div_pos hKL hKpos

/-- A floor quotient loses at most the harmless factor `2K`.  This is the
comparison that pays every support-count-dependent logarithmic loss from the
main mass `mW`. -/
theorem globalActualLogScale_le_two_mul_divisor_mul_multiplicity
    (D : CarrySeries) {K N : ℕ} (hKpos : 0 < K)
    (hKL : K ≤ globalActualLogScale D N) :
    globalActualLogScale D N ≤
      2 * K * globalActualMultiplicity D K N := by
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  have hmpos : 0 < m := by
    simpa only [m, L] using globalActualMultiplicity_pos D hKpos hKL
  have hdiv : L < L / K * K + K :=
    Nat.lt_div_mul_add (a := L) (b := K) hKpos
  have hmEq : m = L / K := rfl
  rw [← hmEq] at hdiv
  have hKle : K ≤ m * K := by
    calc
      K = 1 * K := by simp
      _ ≤ m * K := Nat.mul_le_mul_right K hmpos
  have hL : L ≤ 2 * (m * K) := by omega
  simpa only [L, m, mul_assoc, mul_left_comm, mul_comm] using hL

/-- Multiplication of two positive-base real powers, in the orientation used
by the census estimates below. -/
theorem rpow_natCast_mul (N : ℕ) (hN : 0 < N) (a b : ℝ) :
    Real.rpow (N : ℝ) a * Real.rpow (N : ℝ) b =
      Real.rpow (N : ℝ) (a + b) := by
  exact (Real.rpow_add
    (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN) a b).symm

/-- Any fixed smaller real power is eventually absorbed by a larger one,
including an arbitrary fixed positive coefficient. -/
theorem eventually_const_mul_rpow_natCast_le_rpow
    (C a b : ℝ) (_hC : 0 < C) (hab : a < b) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.rpow (N : ℝ) a ≤ Real.rpow (N : ℝ) b := by
  have htend : Tendsto
      (fun N : ℕ => Real.rpow (N : ℝ) (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp
      tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      C ≤ Real.rpow (N : ℝ) (b - a) :=
    (tendsto_atTop.1 htend C)
  filter_upwards [hlarge, eventually_ge_atTop 1] with N hCN hN
  have hNpos : 0 < N := by omega
  calc
    C * Real.rpow (N : ℝ) a ≤
        Real.rpow (N : ℝ) (b - a) * Real.rpow (N : ℝ) a :=
      mul_le_mul_of_nonneg_right hCN (Real.rpow_nonneg (by positivity) _)
    _ = Real.rpow (N : ℝ) ((b - a) + a) :=
      rpow_natCast_mul N hNpos (b - a) a
    _ = Real.rpow (N : ℝ) b := by congr 1; ring

/-- A power below the admissible exponent is bounded by the window width. -/
theorem rpow_natCast_le_admissibleWidth {θ a : ℝ} {N W : ℕ}
    (ha : a ≤ θ) (hwindow : AdmissibleWindow θ N W) :
    Real.rpow (N : ℝ) a ≤ (W : ℝ) := by
  have hNbase : (1 : ℝ) ≤ N := by exact_mod_cast hwindow.1
  exact (Real.rpow_le_rpow_of_exponent_le hNbase ha).trans hwindow.2.1

/-- One fixed logarithmic-square coefficient dominating every elementary
finite-scale side condition in the final argument. -/
def globalActualSideSlope (D : CarrySeries) (Cgap : ℕ) : ℕ :=
  2 * globalActualGapSlope D Cgap +
    globalActualLockingSlope D + globalActualContinuationSlope D +
    globalActualBlockSlope D + 3

theorem globalActualSideSlope_pos (D : CarrySeries) (Cgap : ℕ) :
    0 < globalActualSideSlope D Cgap := by
  unfold globalActualSideSlope
  omega

/-- Positive degree is already paid by the canonical continuation span. -/
theorem degree_le_globalActualInteriorContinuationSpan (D : CarrySeries)
    (hd : 0 < D.weight.natDegree) (N : ℕ) :
    D.weight.natDegree ≤ globalActualInteriorContinuationSpan D N := by
  unfold globalActualInteriorContinuationSpan
    globalActualInteriorCoalescencePolynomialExponent
  have hlog : 1 ≤ Nat.log D.base (5 * N + 1) + 1 := by omega
  have hmul : 2 * D.weight.natDegree ≤
      (2 * vandermondeExponent D.weight.natDegree +
          2 * D.weight.natDegree) *
        (Nat.log D.base (5 * N + 1) + 1) := by
    calc
      2 * D.weight.natDegree =
          (2 * D.weight.natDegree) * 1 := by ring
      _ ≤ (2 * D.weight.natDegree) *
          (Nat.log D.base (5 * N + 1) + 1) :=
        Nat.mul_le_mul_left _ hlog
      _ ≤ (2 * vandermondeExponent D.weight.natDegree +
            2 * D.weight.natDegree) *
          (Nat.log D.base (5 * N + 1) + 1) := by
        apply Nat.mul_le_mul_right
        omega
  omega

/-- The canonical logarithmic choices satisfy all geometry, stabilization and
high-frequency interval side conditions uniformly on admissible windows. -/
theorem eventually_globalActualCanonicalSideConditions
    (D : CarrySeries) (Cgap K : ℕ) {θ β : ℝ}
    (hd : 0 < D.weight.natDegree) (_hKpos : 0 < K)
    (hβ : 0 < β) (hβθ : β ≤ θ) :
    ∀ᶠ N : ℕ in atTop, ∀ W : ℕ, AdmissibleWindow θ N W →
      let L := globalActualLogScale D N
      let m := globalActualMultiplicity D K N
      let cap := globalActualGapEnvelope D Cgap N
      let F := globalActualInteriorContinuationSpan D N
      K ≤ L ∧
      2 * D.weight.natDegree + 1 ≤ L ∧
      D.positiveFrom ≤ N ∧
      lockingThreshold D N + cap ≤ N ∧
      (m + 1) *
          (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) < N ∧
      m * cap ≤ N ∧ F ≤ N ∧
      globalActualInteriorBlockScaleCap D N W cap ≤ N ∧
      globalActualInteriorSampleIntervalCap D N W m cap F + 1 ≤ 2 * W := by
  let C := globalActualSideSlope D Cgap
  have hsmall := eventually_globalActualLogScale_power_le_rpow
    D (C : ℝ) 2 β (by exact_mod_cast globalActualSideSlope_pos D Cgap) hβ
  have hlargeL : ∀ᶠ N : ℕ in atTop,
      max K (2 * D.weight.natDegree + 1) ≤ globalActualLogScale D N :=
    (globalActualLogScale_tendsto_atTop D).eventually_ge_atTop
      (max K (2 * D.weight.natDegree + 1))
  filter_upwards [hsmall, hlargeL, eventually_ge_atTop D.positiveFrom] with
      N hsmallN hlargeN hpositive
  intro W hwindow
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  let cap := globalActualGapEnvelope D Cgap N
  let F := globalActualInteriorContinuationSpan D N
  have hL : 1 ≤ L := globalActualLogScale_pos D N
  have hKL : K ≤ L := (le_max_left _ _).trans hlargeN
  have hUL : 2 * D.weight.natDegree + 1 ≤ L :=
    (le_max_right _ _).trans hlargeN
  have hW : W ≤ N := hwindow.2.2
  have hm : m ≤ L := by
    dsimp only [m, globalActualMultiplicity, L]
    exact Nat.div_le_self _ _
  have hcap : cap ≤ globalActualGapSlope D Cgap * L := by
    dsimp only [cap, L]
    exact globalActualGapEnvelope_le_slope_mul D Cgap N
  have hlock : lockingThreshold D N ≤
      globalActualLockingSlope D * L := by
    simpa only [L] using lockingThreshold_le_slope_mul D N
  have hF : F ≤ globalActualContinuationSlope D * L := by
    dsimp only [F, L]
    exact (globalActualInteriorContinuationSpan_le_envelope D N).trans
      (globalActualContinuationEnvelope_le_slope_mul D N)
  have hsideReal : ((C * L ^ 2 : ℕ) : ℝ) ≤ (W : ℝ) := by
    calc
      ((C * L ^ 2 : ℕ) : ℝ) ≤ Real.rpow (N : ℝ) β := by
        simpa only [C, L, Nat.cast_mul, Nat.cast_pow] using hsmallN
      _ ≤ (W : ℝ) := rpow_natCast_le_admissibleWidth hβθ hwindow
  have hside : C * L ^ 2 ≤ W := by exact_mod_cast hsideReal
  have hLL : L ≤ L ^ 2 := by
    calc
      L = L * 1 := by simp
      _ ≤ L * L := Nat.mul_le_mul_left L hL
      _ = L ^ 2 := by ring
  have hlockGapCoeff : globalActualLockingSlope D +
      globalActualGapSlope D Cgap ≤ C := by
    dsimp only [C, globalActualSideSlope]
    omega
  have hscalePoly : globalActualLockingSlope D * L +
      globalActualGapSlope D Cgap * L ≤ C * L ^ 2 := by
    calc
      _ = (globalActualLockingSlope D +
          globalActualGapSlope D Cgap) * L := by ring
      _ ≤ C * L := Nat.mul_le_mul_right L hlockGapCoeff
      _ ≤ C * L ^ 2 := Nat.mul_le_mul_left C hLL
  have hscaleSide : lockingThreshold D N + cap ≤ C * L ^ 2 := by
    calc
      lockingThreshold D N + cap ≤
          globalActualLockingSlope D * L +
            globalActualGapSlope D Cgap * L := Nat.add_le_add hlock hcap
      _ ≤ C * L ^ 2 := hscalePoly
  have hblock : globalActualInteriorBlockScaleCap D N W cap ≤
      globalActualBlockSlope D * L := by
    exact (globalActualInteriorBlockScaleCap_le_envelope D hW
      (hscaleSide.trans (hside.trans hW))).trans
      (globalActualBlockScaleEnvelope_le_slope_mul D N)
  have hmcap : m * cap ≤ globalActualGapSlope D Cgap * L ^ 2 := by
    calc
      m * cap ≤ L * (globalActualGapSlope D Cgap * L) :=
        Nat.mul_le_mul hm hcap
      _ = globalActualGapSlope D Cgap * L ^ 2 := by ring
  have hactualCap :
      D.weight.natDegree * Nat.log D.base (3 * N) + Cgap ≤ cap := by
    dsimp only [cap]
    exact actualGapCap_le_globalActualGapEnvelope D Cgap N
  have hmOne : m + 1 ≤ 2 * L := by omega
  have hgeomRaw :
      (m + 1) *
          (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) ≤
        2 * globalActualGapSlope D Cgap * L ^ 2 := by
    calc
      _ ≤ (2 * L) * (globalActualGapSlope D Cgap * L) :=
        Nat.mul_le_mul hmOne (hactualCap.trans hcap)
      _ = 2 * globalActualGapSlope D Cgap * L ^ 2 := by ring
  have hgeomStrict :
      2 * globalActualGapSlope D Cgap * L ^ 2 < C * L ^ 2 := by
    apply Nat.mul_lt_mul_of_pos_right
    · dsimp only [C, globalActualSideSlope]
      omega
    · exact pow_pos (by omega : 0 < L) 2
  have hremainder :
      m * cap + F + globalActualInteriorBlockScaleCap D N W cap + 1 ≤
        C * L ^ 2 := by
    calc
      _ ≤ globalActualGapSlope D Cgap * L ^ 2 +
          globalActualContinuationSlope D * L +
          globalActualBlockSlope D * L + 1 := by
        exact Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hmcap hF) hblock) (le_refl _)
      _ ≤ C * L ^ 2 := by
        calc
          globalActualGapSlope D Cgap * L ^ 2 +
                globalActualContinuationSlope D * L +
                globalActualBlockSlope D * L + 1 ≤
              globalActualGapSlope D Cgap * L ^ 2 +
                globalActualContinuationSlope D * L ^ 2 +
                globalActualBlockSlope D * L ^ 2 + L ^ 2 := by
            exact Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add (le_refl _)
                  (Nat.mul_le_mul_left _ hLL))
                (Nat.mul_le_mul_left _ hLL))
              (hL.trans hLL)
          _ = (globalActualGapSlope D Cgap +
                globalActualContinuationSlope D +
                globalActualBlockSlope D + 1) * L ^ 2 := by ring
          _ ≤ C * L ^ 2 := by
            apply Nat.mul_le_mul_right
            dsimp only [C, globalActualSideSlope]
            omega
  have hgapSide : globalActualGapSlope D Cgap * L ^ 2 ≤ C * L ^ 2 := by
    apply Nat.mul_le_mul_right
    dsimp only [C, globalActualSideSlope]
    omega
  have hcontinuationSide : globalActualContinuationSlope D * L ≤
      C * L ^ 2 := by
    calc
      _ ≤ globalActualContinuationSlope D * L ^ 2 :=
        Nat.mul_le_mul_left _ hLL
      _ ≤ C * L ^ 2 := by
        apply Nat.mul_le_mul_right
        dsimp only [C, globalActualSideSlope]
        omega
  have hblockSide : globalActualBlockSlope D * L ≤ C * L ^ 2 := by
    calc
      _ ≤ globalActualBlockSlope D * L ^ 2 :=
        Nat.mul_le_mul_left _ hLL
      _ ≤ C * L ^ 2 := by
        apply Nat.mul_le_mul_right
        dsimp only [C, globalActualSideSlope]
        omega
  refine ⟨hKL, hUL, hpositive, hscaleSide.trans (hside.trans hW), ?_,
    hmcap.trans (hgapSide.trans (hside.trans hW)),
    hF.trans (hcontinuationSide.trans (hside.trans hW)),
    hblock.trans (hblockSide.trans (hside.trans hW)), ?_⟩
  · exact hgeomRaw.trans_lt <| hgeomStrict.trans_le (hside.trans hW)
  · unfold globalActualInteriorSampleIntervalCap
    change W + m * cap + F +
        globalActualInteriorBlockScaleCap D N W cap + 1 ≤ 2 * W
    omega

/-- Rare prefixes enter their `1/16` component budget once the prefix census
and the remaining logarithmic factor have separate `N^β` bounds. -/
theorem globalActualRareCoarseBound_component_budget
    (D : CarrySeries) {N W m cap : ℕ} {β : ℝ}
    (hN : 0 < N)
    (hprefix : (globalActualPrefixWordCensus D N m cap : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hfactor : ((16 * (D.weight.natDegree + 1) * cap : ℕ) : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hwidth : Real.rpow (N : ℝ) (2 * β) ≤ (W : ℝ)) :
    16 * (globalActualRareCoarseBound D N m cap : ℝ) ≤
      (m * W : ℕ) := by
  have hprod :
      (globalActualPrefixWordCensus D N m cap : ℝ) *
          ((16 * (D.weight.natDegree + 1) * cap : ℕ) : ℝ) ≤
        Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β :=
    mul_le_mul hprefix hfactor
      (show (0 : ℝ) ≤ (16 * (D.weight.natDegree + 1) * cap : ℕ) by positivity)
      (Real.rpow_nonneg (by positivity) β)
  unfold globalActualRareCoarseBound
  push_cast at hprod ⊢
  calc
    16 *
        ((globalActualPrefixWordCensus D N m cap : ℝ) *
          (D.weight.natDegree + 1) * (m * cap)) =
      (m : ℝ) *
        ((globalActualPrefixWordCensus D N m cap : ℝ) *
          (16 * (D.weight.natDegree + 1) * cap)) := by ring
    _ ≤ (m : ℝ) *
        (Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (m : ℝ) * Real.rpow (N : ℝ) (2 * β) := by
      rw [rpow_natCast_mul N hN β β]
      congr 2
      ring
    _ ≤ (m : ℝ) * W := mul_le_mul_of_nonneg_left hwidth (by positivity)

/-- The three exterior word censuses and the paid fibre factor enter their
`1/16` budget after four independent `N^β` absorptions. -/
theorem globalActualExteriorCoarseBound_component_budget
    (D : CarrySeries) {N W m cap threshold : ℕ} {β : ℝ}
    (hN : 0 < N)
    (hprefix : (globalActualPrefixWordCensus D N m cap : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hpre : (globalActualPreExteriorCensus m cap : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hselected : (globalActualSelectedExteriorCensus threshold m cap : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hfibre : globalActualExteriorFibreEnvelope D N W m cap threshold ≤
      3 * D.weight.natDegree)
    (hfactor : ((48 * D.weight.natDegree * cap : ℕ) : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hwidth : Real.rpow (N : ℝ) (4 * β) ≤ (W : ℝ)) :
    16 * globalActualExteriorCoarseBound D N W m cap threshold ≤
      (m * W : ℕ) := by
  have hfibre0 := globalActualExteriorFibreEnvelope_nonneg
    D N W m cap threshold
  have hscaledFibre :
      16 * globalActualExteriorFibreEnvelope D N W m cap threshold *
          (cap : ℝ) ≤ (48 * D.weight.natDegree * cap : ℕ) := by
    calc
      16 * globalActualExteriorFibreEnvelope D N W m cap threshold *
          (cap : ℝ) ≤ 16 * (3 * D.weight.natDegree : ℝ) * cap := by
        gcongr
      _ = (48 * D.weight.natDegree * cap : ℕ) := by push_cast; ring
  have hfour :
      (globalActualPrefixWordCensus D N m cap : ℝ) *
          globalActualPreExteriorCensus m cap *
          globalActualSelectedExteriorCensus threshold m cap *
          (16 * globalActualExteriorFibreEnvelope D N W m cap threshold *
            (cap : ℝ)) ≤
        Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β *
          Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β := by
    have hpow0 : 0 ≤ Real.rpow (N : ℝ) β :=
      Real.rpow_nonneg (by positivity) β
    have h12 := mul_le_mul hprefix hpre
      (show (0 : ℝ) ≤ globalActualPreExteriorCensus m cap by positivity)
      hpow0
    have h123 := mul_le_mul h12 hselected
      (show (0 : ℝ) ≤ globalActualSelectedExteriorCensus threshold m cap by positivity)
      (mul_nonneg hpow0 hpow0)
    have hscaled0 : 0 ≤
        16 * globalActualExteriorFibreEnvelope D N W m cap threshold *
          (cap : ℝ) := by
      exact mul_nonneg (mul_nonneg (by positivity) hfibre0) (by positivity)
    exact mul_le_mul h123 (hscaledFibre.trans hfactor) hscaled0
      (mul_nonneg (mul_nonneg hpow0 hpow0) hpow0)
  unfold globalActualExteriorCoarseBound
  push_cast
  calc
    16 *
        ((globalActualPrefixWordCensus D N m cap : ℝ) *
          globalActualPreExteriorCensus m cap *
          globalActualSelectedExteriorCensus threshold m cap *
          globalActualExteriorFibreEnvelope D N W m cap threshold *
          (m * cap)) =
      (m : ℝ) *
        ((globalActualPrefixWordCensus D N m cap : ℝ) *
          globalActualPreExteriorCensus m cap *
          globalActualSelectedExteriorCensus threshold m cap *
          (16 * globalActualExteriorFibreEnvelope D N W m cap threshold *
            (cap : ℝ))) := by ring
    _ ≤ (m : ℝ) *
        (Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β *
          Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β) :=
      mul_le_mul_of_nonneg_left hfour (by positivity)
    _ = (m : ℝ) * Real.rpow (N : ℝ) (4 * β) := by
      rw [rpow_natCast_mul N hN β β,
        rpow_natCast_mul N hN (β + β) β,
        rpow_natCast_mul N hN (β + β + β) β]
      congr 2
      ring
    _ ≤ (m : ℝ) * W := mul_le_mul_of_nonneg_left hwidth (by positivity)

/-- The endpoint loss is paid by one logarithmic `N^β` factor. -/
theorem globalActualEndpointLoss_component_budget
    {N W m cap : ℕ} {β : ℝ}
    (hfactor : ((16 * m * cap : ℕ) : ℝ) ≤ Real.rpow (N : ℝ) β)
    (hwidth : Real.rpow (N : ℝ) β ≤ (W : ℝ)) :
    16 * ((m * m * cap : ℕ) : ℝ) ≤ (m * W : ℕ) := by
  push_cast at hfactor ⊢
  calc
    16 * ((m : ℝ) * m * cap) = (m : ℝ) * (16 * m * cap) := by ring
    _ ≤ (m : ℝ) * Real.rpow (N : ℝ) β :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ ≤ (m : ℝ) * W := mul_le_mul_of_nonneg_left hwidth (by positivity)

/-- The low-frequency interior census enters its `1/64` budget after one
prefix `N^β` bound and one fixed logarithmic-polynomial `N^β` bound. -/
theorem globalActualInteriorLowCoarseBound_component_budget
    (D : CarrySeries) {N W m cap U L G B : ℕ} {β : ℝ}
    (hN : 0 < N) (hm : m ≤ L) (hmOne : m + 1 ≤ 2 * m)
    (hU : U ≤ L)
    (hlog : Nat.log 2 cap + 1 ≤ (G + 1) * L)
    (hblock : globalActualInteriorBlockScaleCap D N W cap ≤ B * L)
    (hprefix : (globalActualPrefixWordCensus D N m cap : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hpoly : ((1024 * (G + 1) * B * L ^ 4 : ℕ) : ℝ) ≤
      Real.rpow (N : ℝ) β)
    (hwidth : Real.rpow (N : ℝ) (2 * β) ≤ (W : ℝ)) :
    64 * (globalActualInteriorLowCoarseBound D N W m cap U : ℝ) ≤
      (m * W : ℕ) := by
  let P := globalActualPrefixWordCensus D N m cap
  have hfirst :
      P * (m + 1) * (Nat.log 2 cap + 1) ≤
        P * (2 * m) * ((G + 1) * L) := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_left P hmOne) hlog
  have hsecond :
      U * (m + 1) *
          (4 * globalActualInteriorBlockScaleCap D N W cap) ≤
        L * (2 * m) * (4 * (B * L)) := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul hU hmOne)
      (Nat.mul_le_mul_left 4 hblock)
  have hraw :
      64 * globalActualInteriorLowCoarseBound D N W m cap U ≤
        64 * (P * (2 * m) * ((G + 1) * L)) *
          (L * (2 * m) * (4 * (B * L))) := by
    unfold globalActualInteriorLowCoarseBound
    simpa only [P, mul_assoc] using
      Nat.mul_le_mul_left 64 (Nat.mul_le_mul hfirst hsecond)
  have hlowNat :
      64 * globalActualInteriorLowCoarseBound D N W m cap U ≤
        m * P * (1024 * (G + 1) * B * L ^ 4) := by
    calc
      _ ≤ 64 * (P * (2 * m) * ((G + 1) * L)) *
          (L * (2 * m) * (4 * (B * L))) := hraw
      _ = m * P * (1024 * m * (G + 1) * B * L ^ 3) := by ring
      _ ≤ m * P * (1024 * L * (G + 1) * B * L ^ 3) := by
        gcongr
      _ = m * P * (1024 * (G + 1) * B * L ^ 4) := by ring
  have hlowReal :
      64 * (globalActualInteriorLowCoarseBound D N W m cap U : ℝ) ≤
        (m : ℝ) * (P : ℝ) *
          (1024 * (G + 1) * B * L ^ 4 : ℕ) := by
    exact_mod_cast hlowNat
  have hprod : (P : ℝ) *
      (1024 * (G + 1) * B * L ^ 4 : ℕ) ≤
        Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β :=
    mul_le_mul hprefix hpoly (by positivity)
      (Real.rpow_nonneg (by positivity) β)
  calc
    64 * (globalActualInteriorLowCoarseBound D N W m cap U : ℝ) ≤
        (m : ℝ) * (P : ℝ) *
          (1024 * (G + 1) * B * L ^ 4 : ℕ) := hlowReal
    _ ≤ (m : ℝ) *
        (Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) β) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hprod
          (show (0 : ℝ) ≤ (m : ℝ) by positivity)
    _ = (m : ℝ) * Real.rpow (N : ℝ) (2 * β) := by
      rw [rpow_natCast_mul N hN β β]
      congr 2
      ring
    _ ≤ (m : ℝ) * W := mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = (m * W : ℕ) := by push_cast; rfl

/-- Generic payment for every term of the form `scale * count * O(L)`.  The
density denominator is chosen so its count inequality and the elementary
quotient comparison `L ≤ 2Km` imply the desired component budget. -/
theorem scaledCountLogLoss_component_budget
    {scale K A q L m M W loss : ℕ}
    (hL : L ≤ 2 * K * m) (hloss : loss ≤ q * L)
    (hcount : ((128 * K * A : ℕ) : ℝ) * (M : ℝ) ≤ (W : ℝ))
    (hcoeff : 2 * scale * K * q ≤ 128 * K * A) :
    (scale : ℝ) * (M : ℝ) * (loss : ℝ) ≤ (m * W : ℕ) := by
  have hlossNat : loss ≤ q * (2 * K * m) :=
    hloss.trans (Nat.mul_le_mul_left q hL)
  have hlossReal : (loss : ℝ) ≤ (q * (2 * K * m) : ℕ) := by
    exact_mod_cast hlossNat
  have hcoeffReal : ((2 * scale * K * q : ℕ) : ℝ) ≤
      (128 * K * A : ℕ) := by exact_mod_cast hcoeff
  calc
    (scale : ℝ) * M * loss ≤
        (scale : ℝ) * M * (q * (2 * K * m) : ℕ) :=
      mul_le_mul_of_nonneg_left hlossReal (by positivity)
    _ = ((2 * scale * K * q : ℕ) : ℝ) * M * m := by
      push_cast
      ring
    _ ≤ ((128 * K * A : ℕ) : ℝ) * M * m := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeffReal (by positivity)) (by positivity)
    _ ≤ (W : ℝ) * m := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (m * W : ℕ) := by push_cast; ring

/-- All fixed polylogarithmic factors remaining after the three census bounds
are simultaneously swallowed by one further `N^β`. -/
theorem eventually_globalActualFinalPolynomialFactors
    (D : CarrySeries) (Cgap K : ℕ) {β : ℝ}
    (hd : 0 < D.weight.natDegree) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop,
      let L := globalActualLogScale D N
      let m := globalActualMultiplicity D K N
      let cap := globalActualGapEnvelope D Cgap N
      ((16 * (D.weight.natDegree + 1) * cap : ℕ) : ℝ) ≤
          Real.rpow (N : ℝ) β ∧
      ((48 * D.weight.natDegree * cap : ℕ) : ℝ) ≤
          Real.rpow (N : ℝ) β ∧
      ((1024 * (globalActualGapSlope D Cgap + 1) *
          globalActualBlockSlope D * L ^ 4 : ℕ) : ℝ) ≤
          Real.rpow (N : ℝ) β ∧
      ((16 * m * cap : ℕ) : ℝ) ≤ Real.rpow (N : ℝ) β := by
  let G := globalActualGapSlope D Cgap
  let B := globalActualBlockSlope D
  let Crare : ℝ := 16 * (D.weight.natDegree + 1) * G
  let Cexterior : ℝ := 48 * D.weight.natDegree * G
  let Clow : ℝ := 1024 * (G + 1) * B
  let Cendpoint : ℝ := 16 * G
  have hG : 0 < G := by
    dsimp only [G, globalActualGapSlope]
    omega
  have hB : 0 < B := by
    dsimp only [B, globalActualBlockSlope]
    omega
  have hrareEvent := eventually_globalActualLogScale_power_le_rpow
    D Crare 1 β (by dsimp only [Crare]; positivity) hβ
  have hexteriorEvent := eventually_globalActualLogScale_power_le_rpow
    D Cexterior 1 β (by dsimp only [Cexterior]; positivity) hβ
  have hlowEvent := eventually_globalActualLogScale_power_le_rpow
    D Clow 4 β (by dsimp only [Clow]; positivity) hβ
  have hendpointEvent := eventually_globalActualLogScale_power_le_rpow
    D Cendpoint 2 β (by dsimp only [Cendpoint]; positivity) hβ
  filter_upwards [hrareEvent, hexteriorEvent, hlowEvent,
      hendpointEvent] with N hrareN hexteriorN hlowN hendpointN
  let L := globalActualLogScale D N
  let m := globalActualMultiplicity D K N
  let cap := globalActualGapEnvelope D Cgap N
  have hm : m ≤ L := by
    dsimp only [m, globalActualMultiplicity, L]
    exact Nat.div_le_self _ _
  have hcap : cap ≤ G * L := by
    dsimp only [cap, G, L]
    exact globalActualGapEnvelope_le_slope_mul D Cgap N
  have hrareNat : 16 * (D.weight.natDegree + 1) * cap ≤
      (16 * (D.weight.natDegree + 1) * G) * L :=
    by simpa only [mul_assoc] using
      Nat.mul_le_mul_left (16 * (D.weight.natDegree + 1)) hcap
  have hexteriorNat : 48 * D.weight.natDegree * cap ≤
      (48 * D.weight.natDegree * G) * L :=
    by simpa only [mul_assoc] using
      Nat.mul_le_mul_left (48 * D.weight.natDegree) hcap
  have hendpointNat : 16 * m * cap ≤ 16 * G * L ^ 2 := by
    calc
      16 * m * cap ≤ 16 * L * (G * L) := by gcongr
      _ = 16 * G * L ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcast :
        ((16 * (D.weight.natDegree + 1) * cap : ℕ) : ℝ) ≤
          ((16 * (D.weight.natDegree + 1) * G) * L : ℕ) := by
      exact_mod_cast hrareNat
    exact hcast.trans <| by
      simpa only [Crare, G, L, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, pow_one] using hrareN
  · have hcast : ((48 * D.weight.natDegree * cap : ℕ) : ℝ) ≤
        ((48 * D.weight.natDegree * G) * L : ℕ) := by
      exact_mod_cast hexteriorNat
    exact hcast.trans <| by
      simpa only [Cexterior, G, L, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, pow_one] using hexteriorN
  · simpa only [Clow, G, B, L, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hlowN
  · have hcast : ((16 * m * cap : ℕ) : ℝ) ≤
        ((16 * G * L ^ 2 : ℕ) : ℝ) := by exact_mod_cast hendpointNat
    exact hcast.trans <| by
      simpa only [Cendpoint, G, L, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat] using hendpointN

/-- Sum of the three slopes multiplying the actual support count in the final
coarse error. -/
def globalActualDensityLossSlope (D : CarrySeries)
    (Cgap reserve : ℕ) : ℕ :=
  1 + globalActualClassificationSlope D Cgap reserve +
    globalActualTerminalSlope D +
    globalActualAssemblySlope D Cgap reserve

theorem globalActualDensityLossSlope_pos (D : CarrySeries)
    (Cgap reserve : ℕ) :
    0 < globalActualDensityLossSlope D Cgap reserve := by
  unfold globalActualDensityLossSlope
  omega

theorem globalActualDensityLossSlope_eq_of_core
    (D E : CarrySeries) (Cgap reserve : ℕ) (hbase : D.base = E.base)
    (hweight : D.weight = E.weight) (hden : D.denominator = E.denominator) :
    globalActualDensityLossSlope D Cgap reserve =
      globalActualDensityLossSlope E Cgap reserve := by
  unfold globalActualDensityLossSlope globalActualClassificationSlope
    globalActualTerminalSlope globalActualAssemblySlope
    globalActualThresholdSlope
  rw [globalActualStateSlope_eq_of_core D E hbase hweight hden,
    globalActualGapSlope_eq_of_core D E Cgap hweight,
    globalActualBlockSlope_eq_of_core D E hbase hweight hden,
    globalActualLockingSlope_eq_of_core D E hbase hweight hden,
    globalActualContinuationSlope_eq_of_core D E hbase hweight hden]

/-- Natural denominator of the final density constant. -/
def globalActualDensityDenominator (D : CarrySeries)
    (Cgap reserve K : ℕ) : ℕ :=
  128 * K * globalActualDensityLossSlope D Cgap reserve

theorem globalActualDensityDenominator_pos (D : CarrySeries)
    (Cgap reserve K : ℕ) (hK : 0 < K) :
    0 < globalActualDensityDenominator D Cgap reserve K := by
  unfold globalActualDensityDenominator
  exact Nat.mul_pos (Nat.mul_pos (by decide) hK)
    (globalActualDensityLossSlope_pos D Cgap reserve)

/-- Explicit fixed density constant used in the positive-degree proof. -/
noncomputable def globalActualDensityConstant (D : CarrySeries)
    (Cgap reserve K : ℕ) : ℝ :=
  1 / globalActualDensityDenominator D Cgap reserve K

theorem globalActualDensityConstant_pos (D : CarrySeries)
    (Cgap reserve K : ℕ) (hK : 0 < K) :
    0 < globalActualDensityConstant D Cgap reserve K := by
  unfold globalActualDensityConstant
  exact one_div_pos.mpr <| by
    exact_mod_cast globalActualDensityDenominator_pos D Cgap reserve K hK

/-- A violation of the claimed density bound gives the count payment consumed
by all three logarithmic loss budgets. -/
theorem globalActualDensityConstant_count_payment
    (D : CarrySeries) (Cgap reserve K : ℕ) (hK : 0 < K)
    {M W : ℕ}
    (hcount : (M : ℝ) <
      globalActualDensityConstant D Cgap reserve K * W) :
    (globalActualDensityDenominator D Cgap reserve K : ℝ) * M ≤ W := by
  let Z := globalActualDensityDenominator D Cgap reserve K
  have hZ : 0 < Z := globalActualDensityDenominator_pos D Cgap reserve K hK
  have hZreal : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hmul := mul_le_mul_of_nonneg_left hcount.le hZreal.le
  calc
    (Z : ℝ) * M ≤ (Z : ℝ) *
        (globalActualDensityConstant D Cgap reserve K * W) := hmul
    _ = (W : ℝ) := by
      dsimp only [globalActualDensityConstant, Z]
      have hne :
          (globalActualDensityDenominator D Cgap reserve K : ℝ) ≠ 0 := by
        exact_mod_cast hZ.ne'
      field_simp [hne]

/-- Density constant with every dependence exposed as the two natural
parameters `K` and `A`. -/
noncomputable def globalUniformDensityConstant (K A : ℕ) : ℝ :=
  1 / (128 * K * A : ℕ)

theorem globalUniformDensityConstant_pos {K A : ℕ}
    (hK : 0 < K) (hA : 0 < A) :
    0 < globalUniformDensityConstant K A := by
  unfold globalUniformDensityConstant
  positivity

theorem globalUniformDensityConstant_count_payment {K A M W : ℕ}
    (hK : 0 < K) (hA : 0 < A)
    (hcount : (M : ℝ) < globalUniformDensityConstant K A * W) :
    ((128 * K * A : ℕ) : ℝ) * M ≤ W := by
  have hZ : 0 < 128 * K * A :=
    Nat.mul_pos (Nat.mul_pos (by decide) hK) hA
  have hZreal : (0 : ℝ) < (128 * K * A : ℕ) := by exact_mod_cast hZ
  have hmul := mul_le_mul_of_nonneg_left hcount.le hZreal.le
  calc
    ((128 * K * A : ℕ) : ℝ) * M ≤
        ((128 * K * A : ℕ) : ℝ) *
          (globalUniformDensityConstant K A * W) := hmul
    _ = (W : ℝ) := by
      unfold globalUniformDensityConstant
      have hne : ((128 * K * A : ℕ) : ℝ) ≠ 0 := hZreal.ne'
      field_simp [hne]

/-- Eight independent component budgets imply that the complete coarse error
is strictly smaller than the mass scale.  The factors `64` account for the
outer factor `4` in the interior cover. -/
theorem globalActualFourClassCoarseError_lt_massScale_of_component_bounds
    (D : CarrySeries) {N W m cap reserve F U : ℕ}
    (hmass : 0 < (m * W : ℕ))
    (hshort :
      16 * (globalActualShortMassBound D N W m cap reserve : ℝ) ≤
        (m * W : ℕ))
    (hrare :
      16 * (globalActualRareCoarseBound D N m cap : ℝ) ≤
        (m * W : ℕ))
    (hexterior :
      16 * globalActualExteriorCoarseBound D N W m cap
          (globalActualInteriorThreshold D N W m cap reserve) ≤
        (m * W : ℕ))
    (hlow :
      64 * (globalActualInteriorLowCoarseBound D N W m cap U : ℝ) ≤
        (m * W : ℕ))
    (hhigh :
      64 * globalActualInteriorHighDecayCensusBound
          D N W m cap F reserve ≤
        (m * W : ℕ))
    (hterminal :
      64 * (enumeratedWindowCount D.positiveEnumeration N W : ℝ) *
          (F + 4 * globalActualInteriorBlockScaleCap D N W cap) ≤
        (m * W : ℕ))
    (hassembly :
      16 * (enumeratedWindowCount D.positiveEnumeration N W : ℝ) *
          globalActualInteriorAssemblyLoss D N W m cap reserve ≤
        (m * W : ℕ))
    (hendpoint :
      16 * ((m * m * cap : ℕ) : ℝ) ≤ (m * W : ℕ)) :
    globalActualFourClassCoarseError D N W m cap reserve F U <
      (m * W : ℕ) := by
  unfold globalActualFourClassCoarseError globalActualInteriorCoarseBound
  have hmassReal : (0 : ℝ) < (m * W : ℕ) := by exact_mod_cast hmass
  push_cast at hshort hrare hexterior hlow hhigh hterminal hassembly hendpoint hmassReal ⊢
  linarith

/-! ## Positive-degree completion -/

/-- Parameterized positive-degree contradiction kernel.  All inputs preceding
`D` in the eventual conclusion are exactly the quantities that must be fixed
for the uniform theorem. -/
theorem positiveDegree_window_density_of_parameters (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {θ : ℝ} (hθ : 0 < θ)
    (Cgap reserve K A : ℕ) (hKfour : 4 ≤ K) (hApos : 0 < A)
    (hprefixEntropy :
      (globalActualPrefixSpanSlope D Cgap : ℝ) *
          Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ (θ / 100) / 20)
    (hselectedEntropy :
      (globalActualSelectedSpanSlope D Cgap reserve : ℝ) *
          Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ (θ / 100) / 20)
    (hbranch : 1 / (K : ℝ) ≤ (θ / 100) / 20)
    (hgeometry : ∃ Ngeom : ℕ, ∀ N W m : ℕ,
      Ngeom ≤ N → W ≤ N →
      (m + 1) *
        (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) < N →
      WindowGeometry D.positiveEnumeration N W m
        (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap))
    (hhighUniform : ∀ {N W m cap F : ℕ},
      0 < globalActualInteriorStateDenominatorCap D N W cap →
      globalActualInteriorSampleIntervalCap D N W m cap F + 1 ≤ 2 * W →
      m + 1 ≤ 2 * m →
      globalActualInteriorHighDecayCensusBound D N W m cap F reserve ≤
        (1 / 64 : ℝ) * (m * W))
    (hclassSlope : globalActualClassificationSlope D Cgap reserve ≤ A)
    (hterminalSlope : globalActualTerminalSlope D ≤ A)
    (hassemblySlope : globalActualAssemblySlope D Cgap reserve ≤ A) :
    UniformlyEventually θ fun N W =>
      globalUniformDensityConstant K A * W ≤ windowCount D.support N W := by
  obtain ⟨Ngeom, hgeometry⟩ := hgeometry
  let β : ℝ := θ / 100
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβθ : β ≤ θ := by dsimp only [β]; linarith
  have htwoβθ : 2 * β ≤ θ := by dsimp only [β]; linarith
  have hfourβθ : 4 * β ≤ θ := by dsimp only [β]; linarith
  have hKpos : 0 < K := by omega
  have hprefix := eventually_globalActualPrefixWordCensus_le_rpow
    D Cgap K β hd hKfour hβ (by simpa only [β] using hprefixEntropy)
  have hpre := eventually_globalActualPreExteriorCensus_le_rpow
    D Cgap K β hKpos hβ (by simpa only [β] using hbranch)
  have hselected := eventually_globalActualSelectedExteriorCensus_le_rpow
    D Cgap reserve K β hd hKfour hβ
      (by simpa only [β] using hselectedEntropy)
  have hside := eventually_globalActualCanonicalSideConditions
    D Cgap K hd hKpos hβ hβθ
  have hfactors := eventually_globalActualFinalPolynomialFactors
    D Cgap K hd hβ
  have hheight := eventually_globalActualExteriorHeight_paid
    D Cgap K hd hKpos
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ W : ℕ,
      AdmissibleWindow θ N W →
      globalUniformDensityConstant K A * W ≤ windowCount D.support N W := by
    filter_upwards [hside, hprefix, hpre, hselected, hfactors, hheight,
        eventually_ge_atTop Ngeom] with
      N hsideN hprefixN hpreN hselectedN hfactorsN hheightN hNgeom
    intro W hwindow
    let L := globalActualLogScale D N
    let m := globalActualMultiplicity D K N
    let cap := globalActualGapEnvelope D Cgap N
    let F := globalActualInteriorContinuationSpan D N
    let U := L
    have hsideData := hsideN W hwindow
    dsimp only at hsideData
    rcases hsideData with
      ⟨hKL, hUdegree, hpositiveFrom, hscale, hgeomSmall,
        hmcap, hFN, hblockN, hsample⟩
    have hNpos : 0 < N := hwindow.1
    have hWle : W ≤ N := hwindow.2.2
    have hLpos : 0 < L := globalActualLogScale_pos D N
    have hmpos : 0 < m := by
      dsimp only [m]
      exact globalActualMultiplicity_pos D hKpos hKL
    have hWreal : (0 : ℝ) < W :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hNpos) θ).trans_le hwindow.2.1
    have hWpos : 0 < W := by exact_mod_cast hWreal
    have hmass : 0 < m * W := Nat.mul_pos hmpos hWpos
    have hactualCap :
        D.weight.natDegree * Nat.log D.base (3 * N) + Cgap ≤ cap := by
      dsimp only [cap]
      exact actualGapCap_le_globalActualGapEnvelope D Cgap N
    have hgeomRaw := hgeometry N W m hNgeom hWle hgeomSmall
    have hgeom : WindowGeometry D.positiveEnumeration N W m cap :=
      hgeomRaw.mono_cap hactualCap
    have hcapPos : 0 < cap := by
      dsimp only [cap, globalActualGapEnvelope]
      exact Nat.add_pos_left (Nat.mul_pos hd hLpos) Cgap
    have hQpos :
        0 < globalActualInteriorStateDenominatorCap D N W cap :=
      globalActualInteriorStateDenominatorCap_pos D hw hcapPos
    have hmOne : m + 1 ≤ 2 * m := by omega
    have hblockSlopeBound :
        globalActualInteriorBlockScaleCap D N W cap ≤
          globalActualBlockSlope D * L :=
      (globalActualInteriorBlockScaleCap_le_envelope D hWle hscale).trans
        (globalActualBlockScaleEnvelope_le_slope_mul D N)
    have hlogCap : Nat.log 2 cap + 1 ≤
        (globalActualGapSlope D Cgap + 1) * L := by
      calc
        Nat.log 2 cap + 1 ≤ cap + 1 :=
          Nat.add_le_add_right (Nat.log_le_self 2 cap) 1
        _ ≤ globalActualGapSlope D Cgap * L + L :=
          Nat.add_le_add
            (globalActualGapEnvelope_le_slope_mul D Cgap N) hLpos
        _ = (globalActualGapSlope D Cgap + 1) * L := by ring
    have henvelope :
        globalActualInteriorUniformCoalescenceEnvelope D N W m cap U F <
          (D.base : ℝ) ^ F := by
      dsimp only [U, F]
      exact globalActualInteriorUniformCoalescenceEnvelope_lt_canonical
        D hWle hscale hLpos hmcap hFN hblockN
    have hFdegree : D.weight.natDegree ≤ F := by
      dsimp only [F]
      exact degree_le_globalActualInteriorContinuationSpan D hd N
    have hhighRaw := hhighUniform hQpos hsample hmOne
    have hhighRaw' :
        globalActualInteriorHighDecayCensusBound D N W m cap F reserve ≤
          (1 / 64 : ℝ) * (m * W : ℕ) := by
      simpa only [Nat.cast_mul] using hhighRaw
    have hhighBudget :
        64 * globalActualInteriorHighDecayCensusBound
            D N W m cap F reserve ≤ (m * W : ℕ) := by
      calc
        64 * globalActualInteriorHighDecayCensusBound
              D N W m cap F reserve ≤
            64 * ((1 / 64 : ℝ) * (m * W : ℕ)) :=
          mul_le_mul_of_nonneg_left hhighRaw' (by norm_num)
        _ = (m * W : ℕ) := by push_cast; ring
    have hselectedN' := hselectedN W hWle hscale
    have hheightN' := hheightN W hWle
    have hfibre :
        globalActualExteriorFibreEnvelope D N W m cap
            (globalActualInteriorThreshold D N W m cap reserve) ≤
          3 * D.weight.natDegree :=
      globalActualExteriorFibreEnvelope_le_three_mul_degree
        D hd hw hcapPos hheightN'
    have hfactorData := hfactorsN
    dsimp only at hfactorData
    rcases hfactorData with
      ⟨hrareFactor, hexteriorFactor, hlowFactor, hendpointFactor⟩
    have hwidthβ : Real.rpow (N : ℝ) β ≤ (W : ℝ) :=
      rpow_natCast_le_admissibleWidth hβθ hwindow
    have hwidthTwoβ : Real.rpow (N : ℝ) (2 * β) ≤ (W : ℝ) :=
      rpow_natCast_le_admissibleWidth htwoβθ hwindow
    have hwidthFourβ : Real.rpow (N : ℝ) (4 * β) ≤ (W : ℝ) :=
      rpow_natCast_le_admissibleWidth hfourβθ hwindow
    have hrareBudget := globalActualRareCoarseBound_component_budget
      D hNpos hprefixN hrareFactor hwidthTwoβ
    have hexteriorBudget := globalActualExteriorCoarseBound_component_budget
      D hNpos hprefixN hpreN hselectedN' hfibre hexteriorFactor hwidthFourβ
    have hlowBudget := globalActualInteriorLowCoarseBound_component_budget
      D hNpos (Nat.div_le_self _ _) hmOne (le_refl L) hlogCap
        hblockSlopeBound hprefixN hlowFactor hwidthTwoβ
    have hendpointBudget := globalActualEndpointLoss_component_budget
      hendpointFactor hwidthβ
    by_contra hgoal
    have hbad : (windowCount D.support N W : ℝ) <
        globalUniformDensityConstant K A * W := lt_of_not_ge hgoal
    let M := enumeratedWindowCount D.positiveEnumeration N W
    have hbadM : (M : ℝ) < globalUniformDensityConstant K A * W := by
      simpa only [M, D.enumeratedWindowCount_eq_windowCount] using hbad
    have hcountPayment := globalUniformDensityConstant_count_payment
      hKpos hApos hbadM
    have hLmass : L ≤ 2 * K * m := by
      dsimp only [L, m]
      exact globalActualLogScale_le_two_mul_divisor_mul_multiplicity
        D hKpos hKL
    have hclassification :
        globalActualClassificationCutoff D N W m cap reserve ≤
          globalActualClassificationSlope D Cgap reserve * L :=
      globalActualClassificationCutoff_le_slope_mul
        D hWle hscale (le_refl _) (Nat.div_le_self _ _)
    have hterminal : F +
        4 * globalActualInteriorBlockScaleCap D N W cap ≤
          globalActualTerminalSlope D * L := by
      dsimp only [F, L]
      exact globalActualTerminalLoss_le_slope_mul D hWle hscale
    have hassemblyLoss :
        globalActualInteriorAssemblyLoss D N W m cap reserve ≤
          globalActualAssemblySlope D Cgap reserve * L :=
      globalActualInteriorAssemblyLoss_le_slope_mul
        D hWle hscale (le_refl _) (Nat.div_le_self _ _)
    have hclassCoeff :
        2 * 16 * K * globalActualClassificationSlope D Cgap reserve ≤
          128 * K * A := by
      calc
        _ ≤ 128 * K * globalActualClassificationSlope D Cgap reserve := by
          gcongr
          norm_num
        _ ≤ 128 * K * A := Nat.mul_le_mul_left _ hclassSlope
    have hterminalCoeff :
        2 * 64 * K * globalActualTerminalSlope D ≤ 128 * K * A := by
      calc
        _ = 128 * K * globalActualTerminalSlope D := by ring
        _ ≤ 128 * K * A := Nat.mul_le_mul_left _ hterminalSlope
    have hassemblyCoeff :
        2 * 16 * K * globalActualAssemblySlope D Cgap reserve ≤
          128 * K * A := by
      calc
        _ ≤ 128 * K * globalActualAssemblySlope D Cgap reserve := by
          gcongr
          norm_num
        _ ≤ 128 * K * A := Nat.mul_le_mul_left _ hassemblySlope
    have hshortRaw := scaledCountLogLoss_component_budget
      hLmass hclassification hcountPayment hclassCoeff
    have hshortBudget :
        16 * (globalActualShortMassBound D N W m cap reserve : ℝ) ≤
          (m * W : ℕ) := by
      calc
        16 * (globalActualShortMassBound D N W m cap reserve : ℝ) =
            (16 : ℝ) * (M : ℝ) *
              globalActualClassificationCutoff D N W m cap reserve := by
          unfold globalActualShortMassBound
          dsimp only [M]
          push_cast
          ring
        _ ≤ (m * W : ℕ) := hshortRaw
    have hterminalBudget :
        64 * (M : ℝ) *
            (F + 4 * globalActualInteriorBlockScaleCap D N W cap) ≤
          (m * W : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (scaledCountLogLoss_component_budget
          hLmass hterminal hcountPayment hterminalCoeff)
    have hassemblyBudget :
        16 * (M : ℝ) *
            globalActualInteriorAssemblyLoss D N W m cap reserve ≤
          (m * W : ℕ) :=
      scaledCountLogLoss_component_budget
        hLmass hassemblyLoss hcountPayment hassemblyCoeff
    have herr :=
      globalActualFourClassCoarseError_lt_massScale_of_component_bounds
        D hmass hshortBudget hrareBudget hexteriorBudget hlowBudget
          hhighBudget (by simpa only [M] using hterminalBudget)
          (by simpa only [M] using hassemblyBudget) hendpointBudget
    exact (not_globalActualFourClassCoarseError_lt_massScale
      D hgeom hWle hscale hpositiveFrom hd hw hUdegree hFdegree henvelope) herr
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  exact ⟨N₀, fun N W hN hwindow => hN₀ N hN W hwindow⟩

/-- Every positive-degree integral carry series has a fixed positive density
on all sufficiently large polynomial windows.  This theorem is the completed
fixed-series contradiction kernel used by `thm_main_uniform`. -/
theorem positiveDegree_window_density (D : CarrySeries)
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {θ : ℝ} (hθ : 0 < θ) (_hθone : θ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      UniformlyEventually θ fun N W =>
        c * W ≤ windowCount D.support N W := by
  obtain ⟨Cgap, Ngeom, hgeometry⟩ := D.exists_windowGeometry
  let hhighEps : (0 : ℝ) < 1 / 64 := by norm_num
  let reserve := globalActualInteriorHighSmallReserve D hd (1 / 64) hhighEps
  let β : ℝ := θ / 100
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβθ : β ≤ θ := by dsimp only [β]; linarith
  have htwoβθ : 2 * β ≤ θ := by dsimp only [β]; linarith
  have hfourβθ : 4 * β ≤ θ := by dsimp only [β]; linarith
  let Centropy : ℝ := max
    (globalActualPrefixSpanSlope D Cgap : ℝ)
    (globalActualSelectedSpanSlope D Cgap reserve : ℝ)
  have hCentropy0 : 0 ≤ Centropy := by
    dsimp only [Centropy]
    exact le_trans (by positivity)
      (le_max_left _ _)
  obtain ⟨K, hKfour, hentropy, hbranch⟩ :=
    exists_entropy_divisor Centropy (β / 20) hCentropy0
      (by positivity)
  have hKpos : 0 < K := by omega
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
  have harg0 : (0 : ℝ) ≤ 2 / (K : ℝ) := by positivity
  have harg1 : (2 : ℝ) / K ≤ 1 := by
    rw [div_le_iff₀ hKreal]
    have hKtwo : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
    simpa only [one_mul] using hKtwo
  have hbinary0 : 0 ≤ Erdos260.binaryEntropy (2 / (K : ℝ)) :=
    binaryEntropy_nonneg_on_unit harg0 harg1
  have hprefixEntropy :
      (globalActualPrefixSpanSlope D Cgap : ℝ) *
          Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ β / 20 := by
    exact (mul_le_mul_of_nonneg_right
      (le_max_left _ _) hbinary0).trans hentropy
  have hselectedEntropy :
      (globalActualSelectedSpanSlope D Cgap reserve : ℝ) *
          Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ β / 20 := by
    exact (mul_le_mul_of_nonneg_right
      (le_max_right _ _) hbinary0).trans hentropy
  let c := globalActualDensityConstant D Cgap reserve K
  have hc : 0 < c := by
    simpa only [c] using globalActualDensityConstant_pos D Cgap reserve K hKpos
  refine ⟨c, hc, ?_⟩
  have hside := eventually_globalActualCanonicalSideConditions
    D Cgap K hd hKpos hβ hβθ
  have hprefix := eventually_globalActualPrefixWordCensus_le_rpow
    D Cgap K β hd hKfour hβ hprefixEntropy
  have hpre := eventually_globalActualPreExteriorCensus_le_rpow
    D Cgap K β hKpos hβ hbranch
  have hselected := eventually_globalActualSelectedExteriorCensus_le_rpow
    D Cgap reserve K β hd hKfour hβ hselectedEntropy
  have hfactors := eventually_globalActualFinalPolynomialFactors
    D Cgap K hd hβ
  have hheight := eventually_globalActualExteriorHeight_paid
    D Cgap K hd hKpos
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ W : ℕ,
      AdmissibleWindow θ N W →
      c * W ≤ windowCount D.support N W := by
    filter_upwards [hside, hprefix, hpre, hselected, hfactors, hheight,
        eventually_ge_atTop Ngeom] with
      N hsideN hprefixN hpreN hselectedN hfactorsN hheightN hNgeom
    intro W hwindow
    let L := globalActualLogScale D N
    let m := globalActualMultiplicity D K N
    let cap := globalActualGapEnvelope D Cgap N
    let F := globalActualInteriorContinuationSpan D N
    let U := L
    have hsideData := hsideN W hwindow
    dsimp only at hsideData
    rcases hsideData with
      ⟨hKL, hUdegree, hpositiveFrom, hscale, hgeomSmall,
        hmcap, hFN, hblockN, hsample⟩
    have hNpos : 0 < N := hwindow.1
    have hWle : W ≤ N := hwindow.2.2
    have hLpos : 0 < L := globalActualLogScale_pos D N
    have hmpos : 0 < m := by
      dsimp only [m]
      exact globalActualMultiplicity_pos D hKpos hKL
    have hWreal : (0 : ℝ) < W := by
      exact (Real.rpow_pos_of_pos (by exact_mod_cast hNpos) θ).trans_le
        hwindow.2.1
    have hWpos : 0 < W := by exact_mod_cast hWreal
    have hmass : 0 < m * W := Nat.mul_pos hmpos hWpos
    have hactualCap :
        D.weight.natDegree * Nat.log D.base (3 * N) + Cgap ≤ cap := by
      dsimp only [cap]
      exact actualGapCap_le_globalActualGapEnvelope D Cgap N
    have hgeomRaw := hgeometry N W m hNgeom hWle hgeomSmall
    have hgeom : WindowGeometry D.positiveEnumeration N W m cap :=
      hgeomRaw.mono_cap hactualCap
    have hcapPos : 0 < cap := by
      dsimp only [cap, globalActualGapEnvelope]
      exact Nat.add_pos_left (Nat.mul_pos hd hLpos) Cgap
    have hQpos :
        0 < globalActualInteriorStateDenominatorCap D N W cap :=
      globalActualInteriorStateDenominatorCap_pos D hw hcapPos
    have hmOne : m + 1 ≤ 2 * m := by omega
    have hblockSlope :
        globalActualInteriorBlockScaleCap D N W cap ≤
          globalActualBlockSlope D * L := by
      exact (globalActualInteriorBlockScaleCap_le_envelope D hWle hscale).trans
        (globalActualBlockScaleEnvelope_le_slope_mul D N)
    have hlogCap : Nat.log 2 cap + 1 ≤
        (globalActualGapSlope D Cgap + 1) * L := by
      calc
        Nat.log 2 cap + 1 ≤ cap + 1 :=
          Nat.add_le_add_right (Nat.log_le_self 2 cap) 1
        _ ≤ globalActualGapSlope D Cgap * L + L := by
          exact Nat.add_le_add
            (globalActualGapEnvelope_le_slope_mul D Cgap N) hLpos
        _ = (globalActualGapSlope D Cgap + 1) * L := by ring
    have henvelope :
        globalActualInteriorUniformCoalescenceEnvelope D N W m cap U F <
          (D.base : ℝ) ^ F := by
      dsimp only [U, F]
      exact globalActualInteriorUniformCoalescenceEnvelope_lt_canonical
        D hWle hscale hLpos hmcap hFN hblockN
    have hFdegree : D.weight.natDegree ≤ F := by
      dsimp only [F]
      exact degree_le_globalActualInteriorContinuationSpan D hd N
    have hhighRaw :=
      globalActualInteriorHighDecayCensus_uniform_small_from_reserve
      D hd hw hhighEps
      (N := N) (W := W) (m := m) (cap := cap) (F := F)
      (reserve := reserve) le_rfl hQpos hsample hmOne
    have hhighRaw' :
        globalActualInteriorHighDecayCensusBound D N W m cap F reserve ≤
          (1 / 64 : ℝ) * (m * W : ℕ) := by
      simpa only [Nat.cast_mul] using hhighRaw
    have hhighBudget :
        64 * globalActualInteriorHighDecayCensusBound
            D N W m cap F reserve ≤ (m * W : ℕ) := by
      calc
        64 * globalActualInteriorHighDecayCensusBound
              D N W m cap F reserve ≤
            64 * ((1 / 64 : ℝ) * (m * W : ℕ)) :=
          mul_le_mul_of_nonneg_left hhighRaw' (by norm_num)
        _ = (m * W : ℕ) := by push_cast; ring
    have hselectedN' := hselectedN W hWle hscale
    have hheightN' := hheightN W hWle
    have hfibre :
        globalActualExteriorFibreEnvelope D N W m cap
            (globalActualInteriorThreshold D N W m cap reserve) ≤
          3 * D.weight.natDegree :=
      globalActualExteriorFibreEnvelope_le_three_mul_degree
        D hd hw hcapPos hheightN'
    have hfactorData := hfactorsN
    dsimp only at hfactorData
    rcases hfactorData with
      ⟨hrareFactor, hexteriorFactor, hlowFactor, hendpointFactor⟩
    have hwidthβ : Real.rpow (N : ℝ) β ≤ (W : ℝ) :=
      rpow_natCast_le_admissibleWidth hβθ hwindow
    have hwidthTwoβ : Real.rpow (N : ℝ) (2 * β) ≤ (W : ℝ) :=
      rpow_natCast_le_admissibleWidth htwoβθ hwindow
    have hwidthFourβ : Real.rpow (N : ℝ) (4 * β) ≤ (W : ℝ) :=
      rpow_natCast_le_admissibleWidth hfourβθ hwindow
    have hrareBudget := globalActualRareCoarseBound_component_budget
      D hNpos hprefixN hrareFactor hwidthTwoβ
    have hexteriorBudget := globalActualExteriorCoarseBound_component_budget
      D hNpos hprefixN hpreN hselectedN' hfibre hexteriorFactor hwidthFourβ
    have hlowBudget := globalActualInteriorLowCoarseBound_component_budget
      D hNpos (Nat.div_le_self _ _) hmOne (le_refl L) hlogCap
        hblockSlope hprefixN hlowFactor hwidthTwoβ
    have hendpointBudget := globalActualEndpointLoss_component_budget
      hendpointFactor hwidthβ
    by_contra hgoal
    have hbad : (windowCount D.support N W : ℝ) < c * W :=
      lt_of_not_ge hgoal
    let M := enumeratedWindowCount D.positiveEnumeration N W
    have hbadM : (M : ℝ) <
        globalActualDensityConstant D Cgap reserve K * W := by
      simpa only [M, c, D.enumeratedWindowCount_eq_windowCount] using hbad
    have hcountPayment := globalActualDensityConstant_count_payment
      D Cgap reserve K hKpos hbadM
    let A := globalActualDensityLossSlope D Cgap reserve
    have hcountPayment' : ((128 * K * A : ℕ) : ℝ) * M ≤ W := by
      simpa only [globalActualDensityDenominator, A, M] using hcountPayment
    have hLmass : L ≤ 2 * K * m := by
      dsimp only [L, m]
      exact globalActualLogScale_le_two_mul_divisor_mul_multiplicity
        D hKpos hKL
    have hclassification :
        globalActualClassificationCutoff D N W m cap reserve ≤
          globalActualClassificationSlope D Cgap reserve * L := by
      exact globalActualClassificationCutoff_le_slope_mul
        D hWle hscale (le_refl _) (Nat.div_le_self _ _)
    have hterminal : F +
        4 * globalActualInteriorBlockScaleCap D N W cap ≤
          globalActualTerminalSlope D * L := by
      dsimp only [F, L]
      exact globalActualTerminalLoss_le_slope_mul D hWle hscale
    have hassemblyLoss :
        globalActualInteriorAssemblyLoss D N W m cap reserve ≤
          globalActualAssemblySlope D Cgap reserve * L := by
      exact globalActualInteriorAssemblyLoss_le_slope_mul
        D hWle hscale (le_refl _) (Nat.div_le_self _ _)
    have hclassSlope : globalActualClassificationSlope D Cgap reserve ≤ A := by
      dsimp only [A, globalActualDensityLossSlope]
      omega
    have hterminalSlope : globalActualTerminalSlope D ≤ A := by
      dsimp only [A, globalActualDensityLossSlope]
      omega
    have hassemblySlope : globalActualAssemblySlope D Cgap reserve ≤ A := by
      dsimp only [A, globalActualDensityLossSlope]
      omega
    have hclassCoeff :
        2 * 16 * K * globalActualClassificationSlope D Cgap reserve ≤
          128 * K * A := by
      calc
        _ ≤ 128 * K * globalActualClassificationSlope D Cgap reserve := by
          gcongr
          norm_num
        _ ≤ 128 * K * A := Nat.mul_le_mul_left _ hclassSlope
    have hterminalCoeff :
        2 * 64 * K * globalActualTerminalSlope D ≤ 128 * K * A := by
      calc
        _ = 128 * K * globalActualTerminalSlope D := by ring
        _ ≤ 128 * K * A := Nat.mul_le_mul_left _ hterminalSlope
    have hassemblyCoeff :
        2 * 16 * K * globalActualAssemblySlope D Cgap reserve ≤
          128 * K * A := by
      calc
        _ ≤ 128 * K * globalActualAssemblySlope D Cgap reserve := by
          gcongr
          norm_num
        _ ≤ 128 * K * A := Nat.mul_le_mul_left _ hassemblySlope
    have hshortRaw := scaledCountLogLoss_component_budget
      hLmass hclassification hcountPayment' hclassCoeff
    have hshortBudget :
        16 * (globalActualShortMassBound D N W m cap reserve : ℝ) ≤
          (m * W : ℕ) := by
      calc
        16 * (globalActualShortMassBound D N W m cap reserve : ℝ) =
            (16 : ℝ) * (M : ℝ) *
              globalActualClassificationCutoff D N W m cap reserve := by
          unfold globalActualShortMassBound
          dsimp only [M]
          push_cast
          ring
        _ ≤ (m * W : ℕ) := hshortRaw
    have hterminalBudget :
        64 * (M : ℝ) *
            (F + 4 * globalActualInteriorBlockScaleCap D N W cap) ≤
          (m * W : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (scaledCountLogLoss_component_budget
          hLmass hterminal hcountPayment' hterminalCoeff)
    have hassemblyBudget :
        16 * (M : ℝ) *
            globalActualInteriorAssemblyLoss D N W m cap reserve ≤
          (m * W : ℕ) :=
      scaledCountLogLoss_component_budget
        hLmass hassemblyLoss hcountPayment' hassemblyCoeff
    have herr :=
      globalActualFourClassCoarseError_lt_massScale_of_component_bounds
        D hmass hshortBudget hrareBudget hexteriorBudget hlowBudget
          hhighBudget (by simpa only [M] using hterminalBudget)
          (by simpa only [M] using hassemblyBudget) hendpointBudget
    exact (not_globalActualFourClassCoarseError_lt_massScale
      D hgeom hWle hscale hpositiveFrom hd hw hUdegree hFdegree henvelope) herr
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  exact ⟨N₀, fun N W hN hwindow => hN₀ N hN W hwindow⟩

/-- Internal uniform theorem.  For fixed base, normalized integral weight,
positive-degree data, window exponent and coprime rational denominator, the
density constant is chosen before the carry numerator, support set and
positivity cutoff encoded by `D`. -/
theorem thm_main_uniform
    (b Q : ℕ) (_hb : 2 ≤ b) (_hQ : 0 < Q)
    (w : Polynomial ℤ) (_hwne : w ≠ 0)
    (hd : 0 < w.natDegree) (hwlead : 0 < w.coeff w.natDegree)
    {θ : ℝ} (hθ : 0 < θ) (_hθone : θ ≤ 1)
    (_hcoprime : Nat.Coprime b Q) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : CarrySeries,
      D.base = b → D.weight = w → D.denominator = Q →
      UniformlyEventually θ fun N W =>
        c * W ≤ windowCount D.support N W := by
  by_cases hexists : ∃ D : CarrySeries,
      D.base = b ∧ D.weight = w ∧ D.denominator = Q
  · obtain ⟨D₀, hD₀base, hD₀weight, hD₀den⟩ := hexists
    have hd₀ : 0 < D₀.weight.natDegree := by
      simpa only [hD₀weight] using hd
    have hw₀ : 0 < D₀.weight.coeff D₀.weight.natDegree := by
      simpa only [hD₀weight] using hwlead
    let C := D₀.gapCoefficient
    let Cgap := Nat.clog b C + w.natDegree + 1
    let hhighEps : (0 : ℝ) < 1 / 64 := by norm_num
    let reserve :=
      globalActualInteriorHighSmallReserve D₀ hd₀ (1 / 64) hhighEps
    let β : ℝ := θ / 100
    have hβ : 0 < β := by dsimp only [β]; positivity
    let Centropy : ℝ := max
      (globalActualPrefixSpanSlope D₀ Cgap : ℝ)
      (globalActualSelectedSpanSlope D₀ Cgap reserve : ℝ)
    have hCentropy0 : 0 ≤ Centropy := by
      dsimp only [Centropy]
      exact le_trans (by positivity) (le_max_left _ _)
    obtain ⟨K, hKfour, hentropy, hbranch⟩ :=
      exists_entropy_divisor Centropy (β / 20) hCentropy0
        (by positivity)
    have hKpos : 0 < K := by omega
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    have harg0 : (0 : ℝ) ≤ 2 / (K : ℝ) := by positivity
    have harg1 : (2 : ℝ) / K ≤ 1 := by
      rw [div_le_iff₀ hKreal]
      have hKtwo : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
      simpa only [one_mul] using hKtwo
    have hbinary0 : 0 ≤ Erdos260.binaryEntropy (2 / (K : ℝ)) :=
      binaryEntropy_nonneg_on_unit harg0 harg1
    have hprefixEntropy₀ :
        (globalActualPrefixSpanSlope D₀ Cgap : ℝ) *
            Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ β / 20 :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hbinary0).trans hentropy
    have hselectedEntropy₀ :
        (globalActualSelectedSpanSlope D₀ Cgap reserve : ℝ) *
            Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ β / 20 :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hbinary0).trans hentropy
    let A := globalActualDensityLossSlope D₀ Cgap reserve
    have hApos : 0 < A := by
      simpa only [A] using globalActualDensityLossSlope_pos D₀ Cgap reserve
    let c := globalUniformDensityConstant K A
    have hc : 0 < c := by
      simpa only [c] using globalUniformDensityConstant_pos hKpos hApos
    refine ⟨c, hc, ?_⟩
    intro D hDbase hDweight hDden
    have hbaseCore : D.base = D₀.base := hDbase.trans hD₀base.symm
    have hweightCore : D.weight = D₀.weight := hDweight.trans hD₀weight.symm
    have hdenCore : D.denominator = D₀.denominator :=
      hDden.trans hD₀den.symm
    have hdD : 0 < D.weight.natDegree := by simpa only [hDweight] using hd
    have hwD : 0 < D.weight.coeff D.weight.natDegree := by
      simpa only [hDweight] using hwlead
    have hCpos : 0 < C := by
      simpa only [C] using D₀.gapCoefficient_pos
    have hCheight₀ :
        D₀.heightConstant * (2 : ℝ) ^ D₀.weight.natDegree ≤ (C : ℝ) := by
      dsimp only [C, CarrySeries.gapCoefficient]
      exact Nat.le_ceil _
    have hCheight :
        D.heightConstant * (2 : ℝ) ^ D.weight.natDegree ≤ (C : ℝ) := by
      rw [D.heightConstant_eq_of_core D₀ hbaseCore hweightCore hdenCore,
        hweightCore]
      exact hCheight₀
    obtain ⟨xgap, hgapRaw⟩ :=
      D.eventual_gap_log_bound_of_coefficient C hCpos hCheight
    have hgap : ∀ x : ℕ, xgap ≤ x → ∀ g : ℕ,
        D.IsSupportGap x g →
          g ≤ D.weight.natDegree * Nat.log D.base x + Cgap := by
      intro x hx g hsupportGap
      have hraw := hgapRaw x hx g hsupportGap
      simpa only [Cgap, hDbase, hDweight] using hraw
    have hgeometry := D.exists_windowGeometry_of_gap_bound hgap
    have hgeomReserveEq :
        globalActualInteriorHighGeometricReserve D hdD =
          globalActualInteriorHighGeometricReserve D₀ hd₀ :=
      globalActualInteriorHighGeometricReserve_eq_of_core
        D D₀ hbaseCore hweightCore hdenCore hdD hd₀
    have htailEq : globalActualInteriorHighTail D =
        globalActualInteriorHighTail D₀ :=
      globalActualInteriorHighTail_eq_of_core D D₀ hweightCore hdenCore
    have hhighUniform : ∀ {N W m cap F : ℕ},
        0 < globalActualInteriorStateDenominatorCap D N W cap →
        globalActualInteriorSampleIntervalCap D N W m cap F + 1 ≤ 2 * W →
        m + 1 ≤ 2 * m →
        globalActualInteriorHighDecayCensusBound D N W m cap F reserve ≤
          (1 / 64 : ℝ) * (m * W) := by
      intro N W m cap F hQcap hsample hmOne
      have hgeomReserve :
          globalActualInteriorHighGeometricReserve D hdD ≤ reserve := by
        rw [hgeomReserveEq]
        dsimp only [reserve, globalActualInteriorHighSmallReserve]
        exact le_max_left _ _
      have htailReserve :
          globalActualInteriorHighTailReserve D₀ hd₀ (1 / 64) hhighEps ≤
            reserve := by
        dsimp only [reserve, globalActualInteriorHighSmallReserve]
        exact le_max_right _ _
      have htail₀ := globalActualInteriorHighTailReserve_spec
        D₀ hd₀ (1 / 64) hhighEps reserve htailReserve
      have htailD : globalActualInteriorHighTail D reserve ≤ (1 / 64 : ℝ) := by
        rw [htailEq]
        exact htail₀
      have hraw := globalActualInteriorHighDecayCensus_le_tail_mul_from_reserve
        D hdD hwD hQcap hgeomReserve hsample hmOne
      exact hraw.trans
        (mul_le_mul_of_nonneg_right htailD (by positivity))
    have hprefixEq := globalActualPrefixSpanSlope_eq_of_core
      D D₀ Cgap hbaseCore hweightCore hdenCore
    have hselectedEq := globalActualSelectedSpanSlope_eq_of_core
      D D₀ Cgap reserve hbaseCore hweightCore hdenCore
    have hprefixEntropy :
        (globalActualPrefixSpanSlope D Cgap : ℝ) *
            Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ (θ / 100) / 20 := by
      rw [hprefixEq]
      simpa only [β] using hprefixEntropy₀
    have hselectedEntropy :
        (globalActualSelectedSpanSlope D Cgap reserve : ℝ) *
            Erdos260.binaryEntropy (2 / (K : ℝ)) ≤ (θ / 100) / 20 := by
      rw [hselectedEq]
      simpa only [β] using hselectedEntropy₀
    have hAeq : globalActualDensityLossSlope D Cgap reserve = A := by
      calc
        globalActualDensityLossSlope D Cgap reserve =
            globalActualDensityLossSlope D₀ Cgap reserve :=
          globalActualDensityLossSlope_eq_of_core
            D D₀ Cgap reserve hbaseCore hweightCore hdenCore
        _ = A := rfl
    have hclassSlope : globalActualClassificationSlope D Cgap reserve ≤ A := by
      rw [← hAeq]
      unfold globalActualDensityLossSlope
      omega
    have hterminalSlope : globalActualTerminalSlope D ≤ A := by
      rw [← hAeq]
      unfold globalActualDensityLossSlope
      omega
    have hassemblySlope : globalActualAssemblySlope D Cgap reserve ≤ A := by
      rw [← hAeq]
      unfold globalActualDensityLossSlope
      omega
    have hkernel := positiveDegree_window_density_of_parameters
      D hdD hwD hθ Cgap reserve K A hKfour hApos
        hprefixEntropy hselectedEntropy (by simpa only [β] using hbranch)
        hgeometry hhighUniform hclassSlope hterminalSlope hassemblySlope
    simpa only [c] using hkernel
  · refine ⟨1, by norm_num, ?_⟩
    intro D hDbase hDweight hDden
    exact False.elim <| hexists ⟨D, hDbase, hDweight, hDden⟩

/-! ## Constant weights -/

/-- Degree zero needs no locking argument: the carry height is bounded, hence
all eventual support gaps are bounded by one fixed constant.  This gives the
full polynomial-window conclusion directly. -/
theorem degreeZero_window_density (D : CarrySeries)
    (hdegree : D.weight.natDegree = 0) {θ : ℝ} (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧
      UniformlyEventually θ fun N W =>
        c * W ≤ windowCount D.support N W := by
  obtain ⟨Cgap, Ngeom, hgeom⟩ := D.exists_windowGeometry
  have htend :
      Tendsto (fun N : ℕ => Real.rpow (N : ℝ) θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        ((2 * (Cgap + 1) : ℕ) : ℝ) ≤ Real.rpow (N : ℝ) θ :=
    (tendsto_atTop.1 htend) ((2 * (Cgap + 1) : ℕ) : ℝ)
  obtain ⟨Nrpow, hNrpow⟩ := eventually_atTop.1 hevent
  let c : ℝ := 1 / (2 * (Cgap + 1 : ℕ))
  refine ⟨c, by dsimp [c]; positivity, max Ngeom (max (Cgap + 1) Nrpow), ?_⟩
  intro N W hN hwindow
  have hNgeom : Ngeom ≤ N := (le_max_left _ _).trans hN
  have hNCgap : Cgap + 1 ≤ N :=
    (le_max_left (Cgap + 1) Nrpow).trans
      ((le_max_right Ngeom _).trans hN)
  have hNNrpow : Nrpow ≤ N :=
    (le_max_right (Cgap + 1) Nrpow).trans
      ((le_max_right Ngeom _).trans hN)
  have hsmall :
      (0 + 1) * (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) < N := by
    simp only [hdegree, zero_mul, zero_add, one_mul]
    omega
  have hgeometry := hgeom N W 0 hNgeom hwindow.2.2 hsmall
  have hwidth :=
    WindowGeometry.width_le_count_add_one_mul D.positiveEnumeration hgeometry
  simp only [hdegree, zero_mul, zero_add] at hwidth
  rw [D.enumeratedWindowCount_eq_windowCount] at hwidth
  have hlargeReal :
      ((2 * (Cgap + 1) : ℕ) : ℝ) ≤ (W : ℝ) :=
    (hNrpow N hNNrpow).trans hwindow.2.1
  have hlarge : 2 * (Cgap + 1) ≤ W := by exact_mod_cast hlargeReal
  let K := windowCount D.support N W
  have hwidthReal : (W : ℝ) ≤ (K + 1 : ℕ) * Cgap := by
    exact_mod_cast (by simpa only [K] using hwidth)
  have hlargeReal' : (2 : ℝ) * (Cgap + 1) ≤ W := by
    exact_mod_cast hlarge
  have hmid : (W : ℝ) / 2 ≤ (K : ℝ) * Cgap := by
    push_cast at hwidthReal
    have hgapHalf : (Cgap : ℝ) ≤ (W : ℝ) / 2 := by
      nlinarith [hlargeReal']
    nlinarith [hwidthReal]
  have htarget : (W : ℝ) ≤ (K : ℝ) * (2 * (Cgap + 1 : ℕ)) := by
    have hnonneg : (0 : ℝ) ≤ K := by positivity
    have hgrow : (K : ℝ) * Cgap ≤ (K : ℝ) * (Cgap + 1) := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      norm_num
    have hhalf : (W : ℝ) / 2 ≤ (K : ℝ) * (Cgap + 1) :=
      hmid.trans hgrow
    calc
      (W : ℝ) = 2 * ((W : ℝ) / 2) := by ring
      _ ≤ 2 * ((K : ℝ) * (Cgap + 1)) := by gcongr
      _ = (K : ℝ) * (2 * (Cgap + 1 : ℕ)) := by push_cast; ring
  dsimp [c]
  rw [one_div, inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Cgap + 1 : ℕ))).2
  simpa only [K, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_one] using htarget

/-- The logarithmic gap theorem implies the paper's subpolynomial gap
formulation: every fixed positive power eventually dominates every genuine
support gap. -/
theorem CarrySeries.eventual_gap_rpow_bound (D : CarrySeries)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g → (g : ℝ) ≤ Real.rpow (x : ℝ) ε := by
  obtain ⟨Craw, xgap, hgap⟩ := D.eventual_gap_log_bound
  let Cgap := Craw + 1
  have hCgap : 0 < Cgap := by dsimp only [Cgap]; omega
  have hslopePos : (0 : ℝ) < globalActualGapSlope D Cgap := by
    exact_mod_cast (by
      unfold globalActualGapSlope
      omega : 0 < globalActualGapSlope D Cgap)
  have hpower := eventually_globalActualLogScale_power_le_rpow
    D (globalActualGapSlope D Cgap : ℝ) 1 ε hslopePos hε
  obtain ⟨xpower, hxpower⟩ := eventually_atTop.1 hpower
  refine ⟨max xgap xpower, ?_⟩
  intro x hx g hsupportGap
  have hxgap : xgap ≤ x := (le_max_left _ _).trans hx
  have hxpower' : xpower ≤ x := (le_max_right _ _).trans hx
  have hraw := hgap x hxgap g hsupportGap
  have hgap' : g ≤ D.weight.natDegree * Nat.log D.base x + Cgap := by
    dsimp only [Cgap]
    omega
  have henv :
      D.weight.natDegree * Nat.log D.base x + Cgap ≤
        globalActualGapEnvelope D Cgap x := by
    unfold globalActualGapEnvelope
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left D.weight.natDegree
        (natLog_le_globalActualLogScale D x)) Cgap
  have hslope := globalActualGapEnvelope_le_slope_mul D Cgap x
  have hpowerX := hxpower x hxpower'
  simp only [pow_one] at hpowerX
  calc
    (g : ℝ) ≤ (globalActualGapEnvelope D Cgap x : ℕ) := by
      exact_mod_cast hgap'.trans henv
    _ ≤ (globalActualGapSlope D Cgap : ℕ) *
          globalActualLogScale D x := by exact_mod_cast hslope
    _ ≤ Real.rpow (x : ℝ) ε := hpowerX

/-! ## Public polynomial-window endpoint -/

/-- Polynomial-window density for a rational polynomial weight.  The result
uses the literal public summand and support set; integral normalization and
the finite denominator-absorbing shift occur only inside the proof. -/
theorem thm_main
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℚ) (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ))
    {θ : ℝ} (hθ : 0 < θ) (hθone : θ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      UniformlyEventually θ fun N W =>
        c * W ≤ windowCount S N W := by
  let h : IntegralNormalization p :=
    Classical.choice (exists_integralNormalization hp)
  let D : CarrySeries := h.toCarrySeries b hb S hS η hsum
  obtain ⟨e, hcoprime⟩ := D.shift_denominator_coprime
  let E : CarrySeries := D.shift e
  have hEbase : E.base = b := rfl
  have hEsupport : E.support = shiftedSupport S e := rfl
  have hElead : 0 < E.weight.coeff E.weight.natDegree := by
    change 0 < E.weight.leadingCoeff
    dsimp only [E, CarrySeries.shift]
    rw [shiftedIntegralPolynomial_leadingCoeff]
    exact h.leadingCoeff_pos
  have htail : ∃ c : ℝ, 0 < c ∧
      UniformlyEventually θ fun N W =>
        c * W ≤ windowCount (shiftedSupport S e) N W := by
    by_cases hdegree : E.weight.natDegree = 0
    · obtain ⟨c, hc, hEcount⟩ :=
        degreeZero_window_density E hdegree hθ
      exact ⟨c, hc, by simpa only [hEsupport] using hEcount⟩
    · have hdegreePos : 0 < E.weight.natDegree := Nat.pos_of_ne_zero hdegree
      have hcoprime' : Nat.Coprime b E.denominator := by
        change Nat.Coprime D.base (D.shift e).denominator
        exact hcoprime.symm
      obtain ⟨c, hc, hall⟩ := thm_main_uniform
        b E.denominator hb E.denominator_pos E.weight E.weight_ne_zero
          hdegreePos hElead hθ hθone hcoprime'
      have hEcount := hall E hEbase rfl rfl
      exact ⟨c, hc, by simpa only [hEsupport] using hEcount⟩
  obtain ⟨c, hc, hshift⟩ := htail
  exact ⟨c / 2, div_pos hc (by norm_num),
    uniformlyEventually_windowCount_of_shiftedSupport
      e hθ hθone hc hshift⟩

/-! ## Density and gap consequences -/

/-- A linear bound in every eventual dyadic window forces positive lower
asymptotic density. -/
theorem lowerDensity_pos_of_uniform_window_density
    (S : Set ℕ) {c : ℝ} (hc : 0 < c)
    (hwindow : UniformlyEventually 1 fun N W =>
      c * W ≤ windowCount S N W) :
    0 < lowerDensity S := by
  obtain ⟨N₀, hN₀⟩ := hwindow
  have hevent : ∀ᶠ X : ℕ in atTop, c / 3 ≤ supportRatio S X := by
    refine eventually_atTop.2 ⟨max (2 * N₀) 2, ?_⟩
    intro X hX
    let N := X / 2
    have hXpos : 0 < X := by omega
    have hNpos : 0 < N := by
      dsimp only [N]
      omega
    have hN₀N : N₀ ≤ N := by
      dsimp only [N]
      omega
    have hsum : N + N ≤ X := by
      dsimp only [N]
      omega
    have hadmissible : AdmissibleWindow 1 N N := by
      refine ⟨hNpos, ?_, le_rfl⟩
      exact (Real.rpow_one (N : ℝ)).le
    have hcount := hN₀ N N hN₀N hadmissible
    change c * (N : ℝ) ≤ (windowCount S N N : ℝ) at hcount
    have hprefix := windowCount_le_supportCount_of_add_le S hsum
    have hthirdNat : X ≤ 3 * N := by
      dsimp only [N]
      omega
    have hthird : (X : ℝ) / 3 ≤ (N : ℝ) := by
      have hthirdReal : (X : ℝ) ≤ 3 * (N : ℝ) := by
        exact_mod_cast hthirdNat
      linarith
    have hlinear : (c / 3) * (X : ℝ) ≤
        (Erdos260.supportCount S X : ℝ) := by
      calc
        (c / 3) * (X : ℝ) = c * ((X : ℝ) / 3) := by ring
        _ ≤ c * (N : ℝ) := mul_le_mul_of_nonneg_left hthird hc.le
        _ ≤ (windowCount S N N : ℝ) := hcount
        _ ≤ (Erdos260.supportCount S X : ℝ) := by exact_mod_cast hprefix
    unfold supportRatio
    exact (le_div_iff₀ (by exact_mod_cast hXpos : (0 : ℝ) < X)).2
      (by simpa [mul_comm] using hlinear)
  have hbdd : atTop.IsCoboundedUnder (· ≥ ·) (supportRatio S) :=
    isCoboundedUnder_ge_of_le atTop (supportRatio_le_one S)
  have hlim : c / 3 ≤ lowerDensity S := by
    unfold lowerDensity
    exact le_liminf_of_le hbdd hevent
  exact (div_pos hc (by norm_num)).trans_le hlim

/-- The public main theorem at `θ=1` gives the first assertion of
`cor:erdos`. -/
theorem rational_series_lowerDensity_pos
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℚ) (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ)) :
    0 < lowerDensity S := by
  obtain ⟨c, hc, hwindow⟩ :=
    thm_main b hb p hp S hS η hsum
      (θ := 1) (by norm_num) (by norm_num)
  exact lowerDensity_pos_of_uniform_window_density S hc hwindow

/-- Public logarithmic gap bound, stated only in terms of the original
rational polynomial and support set. -/
theorem rational_series_eventual_gap_log_bound
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℚ) (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ)) :
    ∃ C x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
      SetSupportGap S x g →
        g ≤ p.natDegree * Nat.log b x + C := by
  let h : IntegralNormalization p :=
    Classical.choice (exists_integralNormalization hp)
  let D : CarrySeries := h.toCarrySeries b hb S hS η hsum
  obtain ⟨C, x₀, hgap⟩ := D.eventual_gap_log_bound
  refine ⟨C, x₀, ?_⟩
  intro x hx g hsupportGap
  have hDgap : D.IsSupportGap x g := by
    simpa only [CarrySeries.IsSupportGap, SetSupportGap,
      show D.support = S from rfl] using hsupportGap
  have hbound := hgap x hx g hDgap
  have hdegree : D.weight.natDegree = p.natDegree := h.natDegree_eq
  simpa only [hdegree, show D.base = b from rfl] using hbound

/-- Public form of the subpolynomial gap conclusion. -/
theorem rational_series_eventual_gap_rpow_bound
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℚ) (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
      SetSupportGap S x g → (g : ℝ) ≤ Real.rpow (x : ℝ) ε := by
  let h : IntegralNormalization p :=
    Classical.choice (exists_integralNormalization hp)
  let D : CarrySeries := h.toCarrySeries b hb S hS η hsum
  intro ε hε
  obtain ⟨x₀, hgap⟩ := D.eventual_gap_rpow_bound hε
  refine ⟨x₀, ?_⟩
  intro x hx g hsupportGap
  apply hgap x hx g
  simpa only [CarrySeries.IsSupportGap, SetSupportGap,
    show D.support = S from rfl] using hsupportGap

/-- Paper label `cor:erdos`: positive lower density, the quantitative
logarithmic gap estimate, and its every-positive-power consequence. -/
theorem cor_erdos
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℚ) (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ)) :
    0 < lowerDensity S ∧
      (∃ C x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
        SetSupportGap S x g →
          g ≤ p.natDegree * Nat.log b x + C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
        SetSupportGap S x g →
          (g : ℝ) ≤ Real.rpow (x : ℝ) ε) := by
  exact ⟨rational_series_lowerDensity_pos b hb p hp S hS η hsum,
    rational_series_eventual_gap_log_bound b hb p hp S hS η hsum,
    rational_series_eventual_gap_rpow_bound b hb p hp S hS η hsum⟩

/-- Positive lower density gives the enumeration formulation `a_j ≪ j`,
including one constant that also absorbs the finite initial segment. -/
theorem rational_series_enumeration_linear_bound
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℚ) (hsum : HasSum (polyWeightedTerm b p S) (η : ℝ))
    (e : Erdos260.SupportEnumeration (Erdos260.positiveSupport S)) :
    ∃ C : ℕ, 0 < C ∧ ∀ j : ℕ, e.a j ≤ C * (j + 1) := by
  have hdensity := rational_series_lowerDensity_pos
    b hb p hp S hS η hsum
  let δ : ℝ := lowerDensity S / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδlim : δ < liminf (supportRatio S) atTop := by
    simpa only [δ, lowerDensity] using
      (half_lt_self hdensity)
  have hbddBelow : atTop.IsBoundedUnder (· ≥ ·) (supportRatio S) :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (supportRatio_nonneg S))
  have hevent := eventually_lt_of_lt_liminf hδlim hbddBelow
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hevent
  obtain ⟨C₀, hC₀⟩ := exists_nat_gt (1 / δ)
  have hC₀δ : 1 < (C₀ : ℝ) * δ := by
    exact (div_lt_iff₀ hδ).mp hC₀
  have hC₀pos : 0 < C₀ := by
    have honeDiv : 0 < (1 : ℝ) / δ := by positivity
    exact_mod_cast (honeDiv.trans hC₀)
  let C := max X₀ C₀
  have hCpos : 0 < C := hC₀pos.trans_le (le_max_right _ _)
  have hCδ : 1 < (C : ℝ) * δ := by
    have hcast : (C₀ : ℝ) ≤ (C : ℝ) := by
      exact_mod_cast (le_max_right X₀ C₀)
    exact hC₀δ.trans_le (mul_le_mul_of_nonneg_right hcast hδ.le)
  refine ⟨C, hCpos, ?_⟩
  intro j
  by_cases hlarge : X₀ ≤ e.a j
  · have hratio := hX₀ (e.a j) hlarge
    have hcount : Erdos260.supportCount S (e.a j) = j + 1 := by
      rw [← supportCount_positiveSupport S]
      exact supportCount_enumeration_apply e j
    unfold supportRatio at hratio
    rw [hcount] at hratio
    have hapos : (0 : ℝ) < e.a j := by exact_mod_cast e.positive j
    have hδa : δ * (e.a j : ℝ) < (j + 1 : ℕ) :=
      (lt_div_iff₀ hapos).mp hratio
    have haReal : (e.a j : ℝ) < (C : ℝ) * (j + 1 : ℕ) := by
      calc
        (e.a j : ℝ) = 1 * (e.a j : ℝ) := by ring
        _ < ((C : ℝ) * δ) * (e.a j : ℝ) :=
          mul_lt_mul_of_pos_right hCδ hapos
        _ = (C : ℝ) * (δ * (e.a j : ℝ)) := by ring
        _ < (C : ℝ) * (j + 1 : ℕ) :=
          mul_lt_mul_of_pos_left hδa (by exact_mod_cast hCpos)
    exact_mod_cast haReal.le
  · have haX₀ : e.a j < X₀ := Nat.lt_of_not_ge hlarge
    have hX₀C : X₀ ≤ C := le_max_left _ _
    have hCmul : C ≤ C * (j + 1) := by
      calc
        C = C * 1 := by simp
        _ ≤ C * (j + 1) := Nat.mul_le_mul_left C (by omega)
    exact haX₀.le.trans (hX₀C.trans hCmul)

/-- Contrapositive density criterion: a convergent polynomial Cantor series
on a zero-lower-density support cannot have a rational sum. -/
theorem irrational_of_lowerDensity_eq_zero
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℝ) (hsum : HasSum (polyWeightedTerm b p S) η)
    (hdensity : lowerDensity S = 0) :
    Irrational η := by
  intro hnot
  obtain ⟨q, hqη⟩ := hnot
  have hsumq := hsum
  rw [← hqη] at hsumq
  have hpos := rational_series_lowerDensity_pos
    b hb p hp S hS q hsumq
  rw [hdensity] at hpos
  exact (lt_irrefl 0) hpos

/-- The equivalent enumeration criterion from `cor:erdos`: if `a_j/j` is
unbounded, the sum is irrational. -/
theorem irrational_of_enumerationRatioUnbounded
    (b : ℕ) (hb : 2 ≤ b)
    (p : Polynomial ℚ) (hp : p ≠ 0)
    (S : Set ℕ) (hS : S.Infinite)
    (η : ℝ) (hsum : HasSum (polyWeightedTerm b p S) η)
    (e : Erdos260.SupportEnumeration (Erdos260.positiveSupport S))
    (hunbounded : EnumerationRatioUnbounded e) :
    Irrational η := by
  intro hrat
  obtain ⟨q, hqη⟩ := hrat
  have hsumq := hsum
  rw [← hqη] at hsumq
  obtain ⟨C, hC, hlinear⟩ := rational_series_enumeration_linear_bound
    b hb p hp S hS q hsumq e
  obtain ⟨j, hj⟩ := hunbounded C
  exact (not_lt_of_ge (hlinear j)) hj

end Erdos260.PolynomialWindow
