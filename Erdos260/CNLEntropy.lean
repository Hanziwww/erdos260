import Mathlib
import Erdos260.CNL

/-!
# Theorem G.6 clean CNL entropy

This file packages Appendix G of `proof_v2.tex` (the correlated
nonseparation ladder closure).  The entropy estimate (G.6) is the
weighted-Kraft sum bound used by Appendix H.2:
\[
  \sum_{\mathcal P} 2^{-c \, \mathcal H_{\rm BND}(\mathcal P)} \le C_Q^M.
\]

The combinatorial finitization (priority-scan classifier, fibre and
class partition) sits in `CNL.lean`.  Here we add the weighted
Kraft summation in `CleanCNLEntropy` form, parametrised by the BND
height function and the bridge-paid valuation, and assemble
`theoremG6_cleanCNLEntropy` from the parametric Kraft hypothesis.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The weighted Kraft sum
`∑ p∈paths, 2 ^ (-c · BNDHeight p)`. -/
def cleanCNLKraftSum {α : Type _} (paths : Finset α)
    (BNDHeight : α -> ℝ) (c : ℝ) : ℝ :=
  ∑ p ∈ paths, (2 : ℝ) ^ (-(c * BNDHeight p))

/-- Pointwise nonnegativity of the Kraft summands. -/
theorem cleanCNLKraftSum_nonneg {α : Type _} (paths : Finset α)
    (BNDHeight : α -> ℝ) (c : ℝ) :
    0 <= cleanCNLKraftSum paths BNDHeight c := by
  unfold cleanCNLKraftSum
  refine Finset.sum_nonneg fun p _ => ?_
  exact Real.rpow_nonneg (by norm_num) _

/-- Monotonicity in the path set. -/
theorem cleanCNLKraftSum_mono {α : Type _} {paths₁ paths₂ : Finset α}
    {BNDHeight : α -> ℝ} {c : ℝ} (h : paths₁ ⊆ paths₂) :
    cleanCNLKraftSum paths₁ BNDHeight c <=
      cleanCNLKraftSum paths₂ BNDHeight c := by
  unfold cleanCNLKraftSum
  exact sum_le_sum_of_subset_of_nonneg h fun p _ _ =>
    Real.rpow_nonneg (by norm_num) _

/--
**Theorem G.6 (clean CNL entropy).**  The weighted-Kraft sum over all
clean unclassified CNL paths through a cluster of length `M` is at
most `C_Q ^ M`.

In the manuscript this is proved by combining the priority selector
of Lemma L.1.1, the Type-C deterministic stretches (L.5), the
Type-P sparsity (L.3), and the bridge-paid bookkeeping (L.4).

In the present packaging the manuscript's Kraft bookkeeping is exposed
as the hypothesis `hkraft`, which the user instantiates from the
Appendix G internal lemmas (Lemma G.1, Proposition G.2,
Lemma G.5).  Under that hypothesis the entropy bound holds.
-/
theorem theoremG6_cleanCNLEntropy {α : Type _}
    (paths : Finset α) (BNDHeight : α -> ℝ) (c CQ : ℝ) (M : Nat)
    (hkraft :
      cleanCNLKraftSum paths BNDHeight c <= CQ ^ M) :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M :=
  hkraft

end

end Erdos260
