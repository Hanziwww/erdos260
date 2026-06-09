import Mathlib
import Erdos260.LiftState

/-!
# Appendix G.3: path-level Kraft bound (Proposition G.2) and the G.6 entropy form

Building on the one-step lift Kraft bound `liftOneStepKraft_le`
(`LiftState.lean`, manuscript Lemma G.1 / G.10), this file formalizes the
manuscript's *iteration* of that bound along a depth-`M` correlated
nonseparation ladder (Proposition G.2):
\[
  \sum_{\mathcal P} 2^{-c\,\mathcal H(\mathcal P)} \le C_c^{\,M}.
\]

The abstract device is a finite branching tree on lift exponents: a children
function `S : ℕ → Finset ℕ` and a per-node Kraft weight `w`.  We prove that if
*every* node obeys the one-step Kraft bound `∑_{c ∈ S p} w c ≤ Cc`, then the
total weight of all depth-`M` descent paths is at most `Cc^M`.  Specializing
`w δ = 2^{-c·H(δ)}` and `Cc = (1 - 2^{-c})⁻¹` yields the manuscript entropy
collapse `≤ C_Q^M` of Theorem G.6 unconditionally.

These are real theorems (no `sorry`, no manuscript hypothesis).  What remains
manuscript-conditional is only the identification of the *specific* CNL cluster
branching with this abstract tree (the Type-C/Type-P classifier), tracked
separately.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Depth-`M` path Kraft sum from a root state.  Given the children-set
function `S` and per-node Kraft weight `w`, `pathKraft S w M root` sums, over
all length-`M` descent paths from `root`, the product of the node weights. -/
def pathKraft (S : ℕ → Finset ℕ) (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | (M + 1), root => ∑ c ∈ S root, w c * pathKraft S w M c

@[simp] theorem pathKraft_zero (S : ℕ → Finset ℕ) (w : ℕ → ℝ) (root : ℕ) :
    pathKraft S w 0 root = 1 := rfl

theorem pathKraft_succ (S : ℕ → Finset ℕ) (w : ℕ → ℝ) (M root : ℕ) :
    pathKraft S w (M + 1) root = ∑ c ∈ S root, w c * pathKraft S w M c := rfl

theorem pathKraft_nonneg {S : ℕ → Finset ℕ} {w : ℕ → ℝ}
    (hw : ∀ c, 0 ≤ w c) (M root : ℕ) : 0 ≤ pathKraft S w M root := by
  induction M generalizing root with
  | zero => simp
  | succ n ih =>
      rw [pathKraft_succ]
      refine Finset.sum_nonneg ?_
      intro c _
      exact mul_nonneg (hw c) (ih c)

/-- **Proposition G.2 (path-level Kraft bound).**  If every node satisfies the
one-step Kraft bound `∑_{c ∈ S p} w c ≤ Cc`, the depth-`M` path Kraft sum is at
most `Cc^M`.  This is the manuscript iteration of Lemma G.1. -/
theorem pathKraft_le {S : ℕ → Finset ℕ} {w : ℕ → ℝ} {Cc : ℝ}
    (hw : ∀ c, 0 ≤ w c) (hCc : 0 ≤ Cc)
    (hstep : ∀ p, ∑ c ∈ S p, w c ≤ Cc) :
    ∀ (M root : ℕ), pathKraft S w M root ≤ Cc ^ M := by
  intro M
  induction M with
  | zero => intro root; simp
  | succ n ih =>
      intro root
      rw [pathKraft_succ]
      calc ∑ c ∈ S root, w c * pathKraft S w n c
          ≤ ∑ c ∈ S root, w c * Cc ^ n := by
            refine Finset.sum_le_sum ?_
            intro c _
            exact mul_le_mul_of_nonneg_left (ih c) (hw c)
        _ = (∑ c ∈ S root, w c) * Cc ^ n := by rw [← Finset.sum_mul]
        _ ≤ Cc * Cc ^ n :=
            mul_le_mul_of_nonneg_right (hstep root) (pow_nonneg hCc n)
        _ = Cc ^ (n + 1) := by rw [pow_succ]; ring

/-- **Theorem G.6 entropy form (real).**  For the lift Kraft weight
`w δ = 2^{-c·H(δ)}` with any height function dominating the exponent
(`δ ≤ H δ`), the depth-`M` path Kraft sum over any branching tree is at most
`((1 - 2^{-c})⁻¹)^M`.  This is the unconditional `C_Q^M` entropy collapse,
obtained by iterating the one-step lift Kraft bound. -/
theorem liftPathKraft_le {c : ℝ} (hc : 0 < c) (S : ℕ → Finset ℕ)
    (H : ℕ → ℝ) (hH : ∀ δ : ℕ, (δ : ℝ) ≤ H δ) (M root : ℕ) :
    pathKraft S (fun δ => (2 : ℝ) ^ (-(c * H δ))) M root
      ≤ ((1 - (2 : ℝ) ^ (-c))⁻¹) ^ M := by
  have hlt1 : (2 : ℝ) ^ (-c) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpos : (0 : ℝ) < 2 ^ (-c) := Real.rpow_pos_of_pos (by norm_num) _
  have hCcpos : (0 : ℝ) < (1 - (2 : ℝ) ^ (-c))⁻¹ := by
    apply inv_pos.mpr; linarith
  refine pathKraft_le ?_ (le_of_lt hCcpos) ?_ M root
  · intro _
    exact Real.rpow_nonneg (by norm_num) _
  · intro p
    have hstep : cleanCNLKraftSum (S p) H c ≤ (1 - (2 : ℝ) ^ (-c))⁻¹ :=
      liftOneStepKraft_le hc H (fun δ _ => hH δ)
    simpa [cleanCNLKraftSum] using hstep

end

end Erdos260
