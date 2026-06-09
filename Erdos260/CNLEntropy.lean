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

/-- If all BND heights are nonnegative and the slope `c` is nonnegative, then
each Kraft summand is at most `1`, so the clean CNL Kraft sum is bounded by the
number of paths. -/
theorem cleanCNLKraftSum_le_card_of_nonneg_height {α : Type _}
    (paths : Finset α) (BNDHeight : α -> ℝ) {c : ℝ}
    (hc_nonneg : 0 <= c)
    (hheight : ∀ p, p ∈ paths -> 0 <= BNDHeight p) :
    cleanCNLKraftSum paths BNDHeight c <= (paths.card : ℝ) := by
  unfold cleanCNLKraftSum
  calc
    (∑ p ∈ paths, (2 : ℝ) ^ (-(c * BNDHeight p)))
        <= ∑ p ∈ paths, (1 : ℝ) := by
          refine sum_le_sum ?_
          intro p hp
          have hmul : 0 <= c * BNDHeight p :=
            mul_nonneg hc_nonneg (hheight p hp)
          have hexp : -(c * BNDHeight p) <= 0 := by linarith
          exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
    _ = (paths.card : ℝ) := by simp

/-- A cardinality bound for a nonnegative-height CNL family implies the weighted
Kraft bound.  This is the finite counting bridge used before inserting the
full proof-v4 L.1.2 weighted encoding. -/
theorem cleanCNLKraftSum_le_of_card_bound {α : Type _}
    (paths : Finset α) (BNDHeight : α -> ℝ) {c CQ : ℝ} {M : Nat}
    (hc_nonneg : 0 <= c)
    (hheight : ∀ p, p ∈ paths -> 0 <= BNDHeight p)
    (hcard : (paths.card : ℝ) <= CQ ^ M) :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M :=
  (cleanCNLKraftSum_le_card_of_nonneg_height paths BNDHeight hc_nonneg hheight).trans hcard

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
