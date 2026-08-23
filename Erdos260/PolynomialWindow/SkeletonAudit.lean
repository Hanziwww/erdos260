import Erdos260.PolynomialWindow.Completion

/-!
# Polynomial-window declaration and semantic audit

The first block follows the 31 labels of `EP260_v2.tex` in source order.
The contract aliases below make the quantifier order of the uniform kernel
and both public endpoints machine-checkable.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos260.PolynomialWindow

-- Theorem/proposition labels and displayed formula labels, 31/31.
#check thm_main
#check cor_erdos
#check CarrySeries.lem_carries
#check lem_localscale
#check lem_windows
#check eq_short
#check eq_prefixspan
#check eq_prefixcount_entropy
#check eq_rare
#check CarrySeries.eq_wordrec
#check lem_locking
#check PolynomialGraph.eq_graphden
#check PolynomialGraph.eq_topmap
#check lem_dichotomy
#check prop_exterior
#check eq_sublevel
#check InteriorNumeratorOrbit.eq_denrec
#check InteriorNumeratorOrbit.eq_qz
#check eq_zmin
#check eq_ellbound
#check eq_blockspan
#check eq_cover
#check lem_blocks
#check eq_blockentropy
#check lem_sampling
#check eq_fibre
#check lem_coalescence
#check eq_divisiblegraphs
#check prop_interior
#check eq_cellcount
#check eq_sourcemap

/-- Exact quantifier contract for the denominator-uniform positive-degree
kernel. -/
abbrev UniformKernelContract : Prop :=
  ∀ (b Q : ℕ), 2 ≤ b → 0 < Q →
    ∀ (w : Polynomial ℤ), w ≠ 0 →
      0 < w.natDegree → 0 < w.coeff w.natDegree →
      ∀ {θ : ℝ}, 0 < θ → θ ≤ 1 → Nat.Coprime b Q →
        ∃ c : ℝ, 0 < c ∧ ∀ D : CarrySeries,
          D.base = b → D.weight = w → D.denominator = Q →
          UniformlyEventually θ fun N W =>
            c * W ≤ windowCount D.support N W

example : UniformKernelContract := thm_main_uniform

/-- Exact public main-theorem contract. -/
abbrev PublicMainContract : Prop :=
  ∀ (b : ℕ), 2 ≤ b →
    ∀ (p : Polynomial ℚ), p ≠ 0 →
      ∀ (S : Set ℕ), S.Infinite →
        ∀ (η : ℚ), HasSum (polyWeightedTerm b p S) (η : ℝ) →
          ∀ {θ : ℝ}, 0 < θ → θ ≤ 1 →
            ∃ c : ℝ, 0 < c ∧
              UniformlyEventually θ fun N W =>
                c * W ≤ windowCount S N W

example : PublicMainContract := thm_main

/-- Exact aggregate corollary contract. -/
abbrev PublicCorollaryContract : Prop :=
  ∀ (b : ℕ), 2 ≤ b →
    ∀ (p : Polynomial ℚ), p ≠ 0 →
      ∀ (S : Set ℕ), S.Infinite →
        ∀ (η : ℚ), HasSum (polyWeightedTerm b p S) (η : ℝ) →
          0 < lowerDensity S ∧
            (∃ C x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
              SetSupportGap S x g →
                g ≤ p.natDegree * Nat.log b x + C) ∧
            (∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ,
              ∀ x : ℕ, x₀ ≤ x → ∀ g : ℕ,
                SetSupportGap S x g →
                  (g : ℝ) ≤ Real.rpow (x : ℝ) ε)

example : PublicCorollaryContract := cor_erdos

-- Constant and quadratic weights.
example : (Polynomial.C (7 : ℚ)).natDegree = 0 := by simp

example :
    ((Polynomial.X : Polynomial ℚ) ^ 2 + Polynomial.C 1).natDegree = 2 := by
  exact Polynomial.natDegree_X_pow_add_C

-- Binary and composite bases both satisfy the public arithmetic interfaces.
example : AdmissibleWindow 1 8 8 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  exact (Real.rpow_one (8 : ℝ)).le

example : Nat.Coprime 12 5 := by decide

-- Deleting and translating a finite prefix has the intended support semantics.
example : shiftedSupport {n : ℕ | 5 ≤ n} 5 = Set.univ := by
  ext n
  simp [shiftedSupport]

-- The normalized highest coefficient follows the exact affine update.
example :
    topState (3 : ℚ) ((2 : ℚ) ^ 4 * 6 - 3) =
      (2 : ℚ) ^ 4 * topState 3 6 - 1 := by
  exact topState_update (A := (3 : ℚ)) (θ := (6 : ℚ)) (by norm_num) 2 4

-- Interpolation uniqueness is exercised through the exact finite sample API.
example {p q : Polynomial ℚ} {ι : Type*} [Fintype ι]
    {f : ι → ℚ} (hf : Function.Injective f)
    (heval : ∀ i, p.eval (f i) = q.eval (f i))
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) : p = q :=
  Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q hf heval hcard

-- Block-state recovery remains part of the audited public lemma surface.
#check blockState_unique
#check PolynomialGraph.normalizedTopState_eq_of_commonInteriorBlock

-- Half-open endpoint semantics and the finite-shift count identity.
example : (Finset.Ioc 2 4 : Finset ℕ) = {3, 4} := by decide

example (S : Set ℕ) :
    windowCount (shiftedSupport S 3) 7 5 = windowCount S 10 5 := by
  simpa using windowCount_shiftedSupport S 3 7 5

end Erdos260.PolynomialWindow
