import Mathlib

/-!
# Phase 0 (P0.2): pinned numerical constants from Appendix K.4

This file pins concrete rational values for the manuscript's structural
constants `cQ, cPr, cStar, ξ, κ, c_1, ε, η`, proves their positivity,
and proves the numerical compatibility `cStar · ξ < cPr` used in the
Pass-3 closure of `Erdos260AnalyticInputsAtomic.constantsCompatible`.

The choices are deliberately conservative.  They are *not* the tightest
constants in the manuscript; they are concrete values that satisfy
every numerical inequality recorded in the K.4 hierarchy
(`proof_v2.tex` lines 3937--4022), so that downstream phases need only
arithmetic to discharge their numerical side conditions.

## Pinned values

```
η      = 1/16
ε      = 1/64
c_1    = 1/256
C_drop = 17/16
κ      = C_drop · c_1 · ε   = 17 / (16 · 256 · 64)
cStar  = 2
ξ      = 1/16
cPr    = 1/2
cQ     = 1/8
ρ_D    = 1/4
c_*    = κ · ξ / 64
```

Compatibility checks (all proved):
* `0 < η < 1/10`
* `0 < ε`
* `0 < c_1`
* `1 < C_drop < 2 − η`
* `0 < κ`
* `0 < cStar`, `0 < ξ`
* `cStar · ξ < cPr` (`1/8 < 1/2`)
* `0 < cPr`, `0 < cQ`
* `C_Q · c_* / (ρ_D · κ) < ξ`  (with `C_Q := 1`, conservative)
-/

namespace Erdos260

noncomputable section

/-! ### Pinned manuscript constants -/

/-- Manuscript `η` (order loss in the high-excess split). -/
def manuscriptEta : ℝ := 1 / 16

/-- Manuscript `ε` (pressure threshold parameter). -/
def manuscriptEps : ℝ := 1 / 64

/-- Manuscript `c_1` (admissible block-length coefficient). -/
def manuscriptC1 : ℝ := 1 / 256

/-- Manuscript `C_drop` (truncation ratio in H.4). -/
def manuscriptCdrop : ℝ := 17 / 16

/-- Manuscript `κ` (order constant). -/
def manuscriptKappa : ℝ := manuscriptCdrop * manuscriptC1 * manuscriptEps

/-- Manuscript `C_*` (descent upper accumulator). -/
def manuscriptCstar : ℝ := 2

/-- Manuscript `ξ` (package smallness parameter). -/
def manuscriptXi : ℝ := 1 / 16

/-- Manuscript `c_pr` (pressure lower bound constant). -/
def manuscriptCpr : ℝ := 1 / 2

/-- Manuscript `c_Q` (positive-density constant). -/
def manuscriptCQ : ℝ := 1 / 8

/-- Manuscript `ρ_D` (dense marker density threshold). -/
def manuscriptRhoD : ℝ := 1 / 4

/-- Manuscript `c_*` (failure-hypothesis constant). -/
def manuscriptCstarSmall : ℝ := manuscriptKappa * manuscriptXi / 64

/-! ### Positivity lemmas -/

theorem manuscriptEta_pos : 0 < manuscriptEta := by
  unfold manuscriptEta; norm_num

theorem manuscriptEta_lt_tenth : manuscriptEta < 1 / 10 := by
  unfold manuscriptEta; norm_num

theorem manuscriptEps_pos : 0 < manuscriptEps := by
  unfold manuscriptEps; norm_num

theorem manuscriptC1_pos : 0 < manuscriptC1 := by
  unfold manuscriptC1; norm_num

theorem manuscriptCdrop_lt_two_sub_eta : manuscriptCdrop < 2 - manuscriptEta := by
  unfold manuscriptCdrop manuscriptEta; norm_num

theorem manuscriptCdrop_gt_one : 1 < manuscriptCdrop := by
  unfold manuscriptCdrop; norm_num

theorem manuscriptCdrop_pos : 0 < manuscriptCdrop :=
  lt_trans zero_lt_one manuscriptCdrop_gt_one

theorem manuscriptKappa_pos : 0 < manuscriptKappa := by
  unfold manuscriptKappa
  exact mul_pos (mul_pos manuscriptCdrop_pos manuscriptC1_pos) manuscriptEps_pos

theorem manuscriptCstar_pos : 0 < manuscriptCstar := by
  unfold manuscriptCstar; norm_num

theorem manuscriptXi_pos : 0 < manuscriptXi := by
  unfold manuscriptXi; norm_num

theorem manuscriptCpr_pos : 0 < manuscriptCpr := by
  unfold manuscriptCpr; norm_num

theorem manuscriptCQ_pos : 0 < manuscriptCQ := by
  unfold manuscriptCQ; norm_num

theorem manuscriptRhoD_pos : 0 < manuscriptRhoD := by
  unfold manuscriptRhoD; norm_num

theorem manuscriptCstarSmall_pos : 0 < manuscriptCstarSmall := by
  unfold manuscriptCstarSmall
  exact div_pos (mul_pos manuscriptKappa_pos manuscriptXi_pos) (by norm_num)

/-! ### Numerical compatibility (Phase 1 target) -/

/--
**Manuscript compatibility (Phase 1).**  `C_* · ξ < c_pr`.
With the pinned values: `2 · (1/16) = 1/8 < 1/2 = c_pr`.
-/
theorem manuscript_constantsCompatible :
    manuscriptCstar * manuscriptXi < manuscriptCpr := by
  unfold manuscriptCstar manuscriptXi manuscriptCpr; norm_num

/--
Manuscript K.4 step 6: `C_Q · c_* / (ρ_D · κ) < ξ` with `C_Q = 1`.

This is the dense-marker compatibility needed for Lemma I.4.1; we record
it here as a sanity check that the choice of `c_*` is small enough.
-/
theorem manuscript_densePackCompatible :
    manuscriptCstarSmall / (manuscriptRhoD * manuscriptKappa) < manuscriptXi := by
  -- `c_* = κ * ξ / 64`, so `c_* / (ρ_D κ) = ξ / (64 ρ_D) = ξ / 16 < ξ`.
  unfold manuscriptCstarSmall manuscriptRhoD manuscriptXi
  have hKappa_pos : 0 < manuscriptKappa := manuscriptKappa_pos
  have hRhoKappa_pos : 0 < (1 / 4 : ℝ) * manuscriptKappa := by
    have : (0 : ℝ) < 1 / 4 := by norm_num
    exact mul_pos this hKappa_pos
  rw [div_lt_iff₀ hRhoKappa_pos]
  nlinarith [hKappa_pos]

/-! ### Bundle the pinned constants -/

/-- The pinned manuscript constants packaged with their positivity and
the numerical compatibility used in `Erdos260AnalyticInputsAtomic`. -/
structure Erdos260Constants where
  cQ : ℝ
  cPr : ℝ
  cStar : ℝ
  ξ : ℝ
  cQ_pos : 0 < cQ
  cPr_pos : 0 < cPr
  cStar_pos : 0 < cStar
  ξ_pos : 0 < ξ
  constantsCompatible : cStar * ξ < cPr

/-- The canonical concrete Pass-3 constants. -/
def erdos260Constants : Erdos260Constants where
  cQ := manuscriptCQ
  cPr := manuscriptCpr
  cStar := manuscriptCstar
  ξ := manuscriptXi
  cQ_pos := manuscriptCQ_pos
  cPr_pos := manuscriptCpr_pos
  cStar_pos := manuscriptCstar_pos
  ξ_pos := manuscriptXi_pos
  constantsCompatible := manuscript_constantsCompatible

end

end Erdos260
