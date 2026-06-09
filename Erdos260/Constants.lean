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

/--
Manuscript `C_*` (descent upper accumulator).

**Round Α1**: Adjusted from 2 to 31/16 so that K.4 step 5
`ξ < c_pr / (4 · C_*)` holds **strictly** at the pinned values
(was equality at `C_* = 2`).  Verify:
`4 · (31/16) · (1/16) = 31/64 < 1/2 = c_pr`.  ✓

Still satisfies `C_* · ξ < c_pr`: `(31/16) · (1/16) = 31/256 < 1/2`.
-/
def manuscriptCstar : ℝ := 31 / 16

/-- Manuscript `ξ` (package smallness parameter). -/
def manuscriptXi : ℝ := 1 / 16

/-- Manuscript `c_pr` (pressure lower bound constant). -/
def manuscriptCpr : ℝ := 1 / 2

/-- Manuscript `c_Q` (positive-density constant). -/
def manuscriptCQ : ℝ := 1 / 8

/-- Manuscript `ρ_D` (dense marker density threshold).

**Q-dependence discrepancy (documentation only — value intentionally unchanged).**
This is pinned at the fixed, **Q-independent** value `1/4`, whereas the manuscript's `ρ_D` is
genuinely **Q-dependent**: `proof_v4_unconditional_clean_v5.tex` §I.4 (~line 2965) takes
`ρ_0(Q) = 1/(4Q)`, and the §24 fixed-period density floor is `1/(3Q)` (~line 962).  The pinned `1/4`
is the **`Q = 1` representative**: at `Q = 1` the §24 floor `1/3` dominates `1/4`, so the shared
density atom `ρ_D · L ≤ windowWeight` (see `SDRDensityCore.windowWeight_ge_rhoD_mul_L` and
`windowWeight_density_floor_*`) holds with margin.  For `Q ≥ 2`, however, the genuine floor `1/(3Q)`
falls below `1/4`, so honoring the density atom at general `Q` would require replacing this constant
by a **Q-dependent** `ρ_D` (e.g. `1/(4Q)` or the `1/(3Q)` floor) threaded through every consumer.

That is a structural refactor (it touches the type/abstraction of the constant and all SDR / DensePack
/ Tower consumers), deliberately **deferred**; nothing here changes the value or any field.  The density
*mechanism* (`SDRDensityCore`) is already parametric in `manuscriptRhoD`/the floor `1/(3Q)` and stays
correct under either calibration — only this pinned scalar is the `Q = 1` specialization.

**Re-flag (wave-21; now flagged by multiple workers): recommended standalone refactor.**
`FailingShellPeriodicityCore` proves the genuine §24 fixed-period density floor
`dyadicDigit_density_floor : (1/(3q₀))·t ≤ wt`, where `q₀` is the ODD part of `Q` (`Q = 2^e · q₀`):
powers of two are eventually periodic mod `Q`, so only the odd part governs the orbit period
`t = ord_{q₀}(2)`.  Hence the sharp Q-dependent calibration is `ρ_D = 1/(4q₀)` (exactly the hypothesis
`hcal : manuscriptRhoD ≤ 1/(3q₀)` consumed by `matchedWindow_of_descentMatch`), matching `proof_v4.tex`
Prop 24.3 `ρ₀(Q) = 1/(4Q)` (~line 962) up to the `Q ↦ q₀` odd-part sharpening.  This Q-dependence is
now flagged by multiple workers (`SDRDensityCore`, `FailingShellPeriodicityCore`); replacing the pinned
`1/4` by the Q-dependent `1/(4q₀)` threaded through every SDR / DensePack / Tower consumer is the
**recommended standalone refactor**, deferred here (value intentionally unchanged). -/
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
With the pinned values (**Round Α1**): `(31/16) · (1/16) = 31/256 < 1/2 = c_pr`.
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

theorem manuscriptCdrop_lt_two : manuscriptCdrop < 2 := by
  unfold manuscriptCdrop
  norm_num

theorem manuscriptKappa_lt_xi : manuscriptKappa < manuscriptXi := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps manuscriptXi
  norm_num

theorem manuscriptCstarSmall_lt_xi : manuscriptCstarSmall < manuscriptXi := by
  unfold manuscriptCstarSmall manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps manuscriptXi
  norm_num

theorem manuscriptCstarSmall_le_xi : manuscriptCstarSmall <= manuscriptXi :=
  le_of_lt manuscriptCstarSmall_lt_xi

/-- **Round Α1**: pinned value of `C_* · ξ` is now `31/256` (was `1/8`). -/
theorem manuscriptCstar_mul_xi_eq_31_256 :
    manuscriptCstar * manuscriptXi = (31 / 256 : ℝ) := by
  unfold manuscriptCstar manuscriptXi
  norm_num

/-- **Compatibility alias** to keep downstream callers compiling.
The bound `manuscriptCstar · manuscriptXi ≤ 1/8` still holds since
`31/256 < 32/256 = 1/8`. -/
theorem manuscriptCstar_mul_xi_le_eighth :
    manuscriptCstar * manuscriptXi ≤ (1 / 8 : ℝ) := by
  unfold manuscriptCstar manuscriptXi
  norm_num

theorem manuscriptCpr_eq_half :
    manuscriptCpr = (1 / 2 : ℝ) := by
  unfold manuscriptCpr
  norm_num

/-! ### Additional K.4 numerical chain -/

theorem manuscriptXi_lt_one : manuscriptXi < 1 := by
  unfold manuscriptXi; norm_num

theorem manuscriptCpr_lt_one : manuscriptCpr < 1 := by
  unfold manuscriptCpr; norm_num

theorem manuscriptCQ_lt_one : manuscriptCQ < 1 := by
  unfold manuscriptCQ; norm_num

theorem manuscriptRhoD_lt_one : manuscriptRhoD < 1 := by
  unfold manuscriptRhoD; norm_num

theorem manuscriptEta_add_xi_lt_one :
    manuscriptEta + manuscriptXi < 1 := by
  unfold manuscriptEta manuscriptXi; norm_num

theorem manuscriptEps_lt_xi : manuscriptEps < manuscriptXi := by
  unfold manuscriptEps manuscriptXi; norm_num

theorem manuscriptKappa_lt_one : manuscriptKappa < 1 := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps; norm_num

theorem manuscriptCstar_mul_xi_lt_one :
    manuscriptCstar * manuscriptXi < 1 := by
  unfold manuscriptCstar manuscriptXi; norm_num

theorem manuscriptCstarSmall_lt_cPr :
    manuscriptCstarSmall < manuscriptCpr := by
  unfold manuscriptCstarSmall manuscriptKappa manuscriptCdrop
    manuscriptC1 manuscriptEps manuscriptXi manuscriptCpr
  norm_num

theorem manuscriptCstarSmall_lt_xi_div_eight :
    manuscriptCstarSmall < manuscriptXi / 8 := by
  unfold manuscriptCstarSmall manuscriptKappa manuscriptCdrop
    manuscriptC1 manuscriptEps manuscriptXi
  norm_num

/-! ### K.4 Step 3: cluster encoding constant + chain inequality

`proof_v2.tex §K.4` step 3: choose `c_1 > 0` such that

  `C_Q^{c_1 Y} · 2^{-c_0 η Y} ≤ 2^{-c Y}` for some `c > 0`,

where `C_Q` here is the **cluster encoding constant** (different from
the failure constant `c_0`), bounded by `1` conservatively.  With
`C_Q := 1`, the chain trivializes to `c ≤ c_0 · η`.  We pin
`c_step3 := c_0 · η / 2` to satisfy this strictly.
-/

/-- Manuscript cluster encoding constant `C_Q ≤ 1` (different from the
failure constant `manuscriptCQ = 1/8`).  Pinned conservatively as `1`. -/
def manuscriptCQ_cluster : ℝ := 1

theorem manuscriptCQ_cluster_pos : 0 < manuscriptCQ_cluster := by
  unfold manuscriptCQ_cluster; norm_num

theorem manuscriptCQ_cluster_le_one : manuscriptCQ_cluster ≤ 1 := by
  unfold manuscriptCQ_cluster; exact le_refl _

/-- K.4 step 3 chain exponent `c := c_0 · η / 2`. -/
def manuscriptCStep3 : ℝ := manuscriptCstarSmall * manuscriptEta / 2

theorem manuscriptCStep3_pos : 0 < manuscriptCStep3 := by
  unfold manuscriptCStep3
  exact div_pos (mul_pos manuscriptCstarSmall_pos manuscriptEta_pos) (by norm_num)

theorem manuscriptCStep3_lt_c0_eta :
    manuscriptCStep3 < manuscriptCstarSmall * manuscriptEta := by
  unfold manuscriptCStep3
  have h_pos : 0 < manuscriptCstarSmall * manuscriptEta :=
    mul_pos manuscriptCstarSmall_pos manuscriptEta_pos
  linarith

/--
**K.4 Step 3 chain inequality** (manuscript line 3955–3960).

At pinned constants with `C_Q := 1` and `c := c_0 · η / 2`:

  `C_Q^{c_1 Y} · 2^{-c_0 η Y} ≤ 2^{-c Y}` for all `Y ≥ 0`.

Since `C_Q = 1`, the LHS reduces to `2^{-c_0 η Y}`; since `c < c_0 η`,
the inequality `-c_0 η Y ≤ -c Y` holds for `Y ≥ 0`.
-/
theorem manuscript_step3_chain (Y : ℝ) (hY : 0 ≤ Y) :
    manuscriptCQ_cluster ^ (manuscriptC1 * Y) *
      (2 : ℝ) ^ (- manuscriptCstarSmall * manuscriptEta * Y) ≤
      (2 : ℝ) ^ (- manuscriptCStep3 * Y) := by
  -- Simplify C_Q^x = 1^x = 1.
  have h_one_rpow : manuscriptCQ_cluster ^ (manuscriptC1 * Y) = 1 := by
    unfold manuscriptCQ_cluster
    exact Real.one_rpow _
  rw [h_one_rpow, one_mul]
  -- Need: 2^(-c_0·η·Y) ≤ 2^(-c·Y), i.e., -c_0·η·Y ≤ -c·Y.
  -- Equivalent: c·Y ≤ c_0·η·Y, true since c < c_0·η and Y ≥ 0.
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have h_step3 : manuscriptCStep3 < manuscriptCstarSmall * manuscriptEta :=
    manuscriptCStep3_lt_c0_eta
  nlinarith [h_step3, hY]

/-! ### K.4 Step 4 derived chain

`κ = C_drop · c_1 · ε` with `1 < C_drop < 2 - η`.  Derived inequalities
needed downstream by H.4 iteration and threshold descent.
-/

theorem manuscriptCdrop_sub_one_pos : 0 < manuscriptCdrop - 1 := by
  unfold manuscriptCdrop; norm_num

theorem manuscript_two_sub_eta_sub_cdrop_pos :
    0 < 2 - manuscriptEta - manuscriptCdrop := by
  unfold manuscriptCdrop manuscriptEta; norm_num

theorem manuscriptKappa_eq_cdrop_c1_eps :
    manuscriptKappa = manuscriptCdrop * manuscriptC1 * manuscriptEps := by
  rfl

/-- `c_1 · ε < κ` since `κ = C_drop · c_1 · ε` with `C_drop > 1`. -/
theorem manuscript_c1_eps_lt_kappa :
    manuscriptC1 * manuscriptEps < manuscriptKappa := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps; norm_num

/-- `κ < ε` since `κ = C_drop · c_1 · ε` with `C_drop · c_1 < 1`. -/
theorem manuscriptKappa_lt_eps : manuscriptKappa < manuscriptEps := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps; norm_num

/-! ### K.4 Step 5 (strict at pinned values, Round Α1)

`proof_v2.tex §K.4` step 5: `ξ < c_pr / (4 · C_*)`.

**Round Α1**: Adjusted `manuscriptCstar` from 2 to 31/16 so that the
**strict** inequality holds at pinned values:
`c_pr / (4 · C_*) = (1/2) / (31/4) = 2/31 ≈ 0.0645 > 1/16 = ξ`.

Pinned values: `ξ = 1/16, c_pr = 1/2, C_* = 31/16`.
`c_pr / (4 · C_*) = (1/2) / (31/4) = 2/31 ≈ 0.0645`.
`ξ = 1/16 = 0.0625`.  `0.0625 < 0.0645`.  ✓
-/

theorem manuscriptXi_lt_cPr_div_4cStar :
    manuscriptXi < manuscriptCpr / (4 * manuscriptCstar) := by
  unfold manuscriptXi manuscriptCpr manuscriptCstar
  norm_num

theorem manuscriptXi_le_cPr_div_4cStar :
    manuscriptXi ≤ manuscriptCpr / (4 * manuscriptCstar) :=
  le_of_lt manuscriptXi_lt_cPr_div_4cStar

theorem four_cStar_mul_xi_lt_cPr :
    4 * manuscriptCstar * manuscriptXi < manuscriptCpr := by
  unfold manuscriptCstar manuscriptXi manuscriptCpr; norm_num

/-! ### K.4 H.4 two-step iteration inequalities

`proof_v2.tex §K.4` lines 4002–4019.  The first drop uses
`m_0 = ⌊c_1 · ε · L⌋ < r = ⌊κ · L⌋` because `C_drop > 1`.  After the
drop, `s_1 = (C_drop − 1) · c_1 · ε · L + O(1)`, `Y_1 = (1 − η) · ε · L`,
and `m_1 = s_1 − 1` satisfies `m_1 ≤ c_1 · Y_1` for sufficiently large
`L`, which follows from `C_drop ≤ 2 − η`.
-/

/-- H.4 inequality: `(C_drop − 1) · c_1 · ε ≤ (1 − η) · c_1 · ε`, equivalent
to `C_drop ≤ 2 − η` (the strict `manuscriptCdrop_lt_two_sub_eta` is
enough). -/
theorem manuscript_h4_iteration_chain :
    (manuscriptCdrop - 1) * manuscriptC1 * manuscriptEps ≤
      (1 - manuscriptEta) * manuscriptC1 * manuscriptEps := by
  have h_cd_le : manuscriptCdrop - 1 ≤ 1 - manuscriptEta := by
    have := manuscriptCdrop_lt_two_sub_eta
    linarith
  have h_c1_eps_nn : 0 ≤ manuscriptC1 * manuscriptEps :=
    mul_nonneg manuscriptC1_pos.le manuscriptEps_pos.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h_cd_le manuscriptC1_pos.le) manuscriptEps_pos.le

/-! ### K.4 Step 7 / line 671 (auxiliary `κ` bounds) -/

/-- Manuscript Section 4 (line 671): `κ < 1/(40 Q)` with `Q = 1` gives
`κ < 1/40`.  This is the strongest concrete `κ` bound from the manuscript.
At the pinned `κ ≈ 6.5 × 10⁻⁵`, this holds with huge margin. -/
theorem manuscriptKappa_lt_one_fortieth :
    manuscriptKappa < 1 / 40 := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps; norm_num

/-! ### K.4 auxiliary chain (additional positivity / bounding) -/

theorem manuscriptC1_lt_eps : manuscriptC1 < manuscriptEps := by
  unfold manuscriptC1 manuscriptEps; norm_num

theorem manuscriptC1_lt_one : manuscriptC1 < 1 := by
  unfold manuscriptC1; norm_num

theorem manuscriptEps_lt_one : manuscriptEps < 1 := by
  unfold manuscriptEps; norm_num

theorem manuscriptEta_lt_one : manuscriptEta < 1 := by
  unfold manuscriptEta; norm_num

theorem manuscriptEta_le_xi : manuscriptEta ≤ manuscriptXi := by
  unfold manuscriptEta manuscriptXi; exact le_refl _

theorem manuscriptCdrop_pos_strict : 1 < manuscriptCdrop := manuscriptCdrop_gt_one

theorem manuscriptCstar_gt_one : 1 < manuscriptCstar := by
  unfold manuscriptCstar; norm_num

/-- **Round Α1**: pinned `manuscriptCstar = 31/16` (was 2). -/
theorem manuscriptCstar_eq_31_16 : manuscriptCstar = (31 / 16 : ℝ) := by
  unfold manuscriptCstar; rfl

theorem manuscriptCstar_lt_two : manuscriptCstar < 2 := by
  unfold manuscriptCstar; norm_num

theorem manuscriptKappa_lt_one_sixteenth : manuscriptKappa < 1 / 16 := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps; norm_num

/-! ### Manuscript T₀ threshold

`proof_v2.tex §21 line 284`: the manuscript window threshold is
`T_0 = 2 L + C_Q`, where `C_Q` is a Q-dependent constant.  We pin
`C_Q := 1` here (smallest positive constant); downstream consumers
substitute this into `hAlloc` when using manuscript-style values.
-/

/-- Manuscript `C_Q` constant in `T_0 = 2 L + C_Q`. -/
def manuscriptCQ_T : Nat := 1

theorem manuscriptCQ_T_pos : 0 < manuscriptCQ_T := by
  unfold manuscriptCQ_T; norm_num

/-! ### Convention 2.0a–2.0d: C1-VD variation-drop bookkeeping constants

`proof_v4.tex` Convention (lines 192–284) introduces, after the local
constants, the variation-drop bookkeeping constants used by the new
Appendix N rolling-window Return–Run–Tower closure (Theorem
`thm:trt-chain-compression`):

```
C_step = 16 (C_loc + C_rk + C_sh + C_AP + C_res + C_dp + 1)
H_lift = C_step + c_I + C_loc + C_rk                          (2.0c)
C_◇    = C_loc + C_sh + C_AP + C_res + C_dp + 1               (2.0c)
P_hand = 64 (H_lift + C_◇ + 1)                                (2.0d)
```

with `0 < c_I ≤ C_step/16`, the layer separation (2.0a)

```
C_step − c_I ≥ 15 (C_loc + C_rk + C_sh + C_AP + C_res + C_dp + 1),
```

and the DensePack residual constant (2.0″)

```
C_dp ≥ 4 + 2 c_Y⁻¹ (C_sh + C_AP + C_loc + 2 C_res),   c_Y = ½ ε (1 − η)².
```

The local constants depend only on `Q`; they are pinned conservatively
at `1`.  `C_dp` is pinned at `2000`, comfortably above the (2.0″) floor
`4 + 327680/225 ≈ 1460.4` forced by the pinned `ε = 1/64`, `η = 1/16`.
These constants are faithful encodings of the manuscript Convention;
they are consumed by the Appendix N modules (roadmap Phases B–E). -/

/-- Manuscript `C_loc` (deterministic boundary/terminal-label loss coefficient). -/
def manuscriptCloc : ℝ := 1

/-- Manuscript `C_rk` (rank-to-threshold surplus loss coefficient). -/
def manuscriptCrk : ℝ := 1

/-- Manuscript `C_sh` (shell margin coefficient). -/
def manuscriptCsh : ℝ := 1

/-- Manuscript `C_AP` (AP-fibre margin coefficient). -/
def manuscriptCAP : ℝ := 1

/-- Manuscript `C_res` (shell-paid reserve coefficient, Definition K.1.2). -/
def manuscriptCres : ℝ := 1

/-- Manuscript active-floor coefficient `c_Y = ½ ε (1 − η)²` (Convention 2.0′). -/
def manuscriptCY : ℝ := manuscriptEps * (1 - manuscriptEta) ^ 2 / 2

/-- Manuscript `C_dp` (DensePack residual constant, Convention 2.0″).  Pinned
at `2000`, above the floor forced by the pinned `ε, η`. -/
def manuscriptCdp : ℝ := 2000

/-- Manuscript `C_gap` (dyadic gap-bound constant in `W_k^{(s)} ≤ C_gap s L + O_Q(s)`). -/
def manuscriptCgap : ℝ := 2

/-- Manuscript `C_step` (layer step coefficient, Convention line 232). -/
def manuscriptCstep : ℝ :=
  16 * (manuscriptCloc + manuscriptCrk + manuscriptCsh + manuscriptCAP +
        manuscriptCres + manuscriptCdp + 1)

/-- Manuscript `c_I` (layer width coefficient, `0 < c_I ≤ C_step/16`). -/
def manuscriptCI : ℝ := 1

/-- Manuscript `H_lift` (C1-VD lift-height coefficient, Convention 2.0c). -/
def manuscriptHlift : ℝ :=
  manuscriptCstep + manuscriptCI + manuscriptCloc + manuscriptCrk

/-- Manuscript `C_◇` (C1-VD diamond coefficient, Convention 2.0c). -/
def manuscriptCdiamond : ℝ :=
  manuscriptCloc + manuscriptCsh + manuscriptCAP + manuscriptCres + manuscriptCdp + 1

/-- Manuscript `P_hand` (primitive-run hand-off period coefficient, Convention 2.0d). -/
def manuscriptPhand : ℝ :=
  64 * (manuscriptHlift + manuscriptCdiamond + 1)

theorem manuscriptCloc_pos : 0 < manuscriptCloc := by unfold manuscriptCloc; norm_num
theorem manuscriptCrk_pos : 0 < manuscriptCrk := by unfold manuscriptCrk; norm_num
theorem manuscriptCsh_pos : 0 < manuscriptCsh := by unfold manuscriptCsh; norm_num
theorem manuscriptCAP_pos : 0 < manuscriptCAP := by unfold manuscriptCAP; norm_num
theorem manuscriptCres_pos : 0 < manuscriptCres := by unfold manuscriptCres; norm_num
theorem manuscriptCdp_pos : 0 < manuscriptCdp := by unfold manuscriptCdp; norm_num
theorem manuscriptCgap_pos : 0 < manuscriptCgap := by unfold manuscriptCgap; norm_num

/-- The active-floor coefficient evaluates to `c_Y = 225/32768`. -/
theorem manuscriptCY_eq : manuscriptCY = 225 / 32768 := by
  unfold manuscriptCY manuscriptEps manuscriptEta; norm_num

theorem manuscriptCY_pos : 0 < manuscriptCY := by
  rw [manuscriptCY_eq]; norm_num

theorem manuscriptCstep_eq : manuscriptCstep = 32096 := by
  unfold manuscriptCstep manuscriptCloc manuscriptCrk manuscriptCsh manuscriptCAP
    manuscriptCres manuscriptCdp
  norm_num

theorem manuscriptCstep_pos : 0 < manuscriptCstep := by
  rw [manuscriptCstep_eq]; norm_num

theorem manuscriptCI_pos : 0 < manuscriptCI := by unfold manuscriptCI; norm_num

theorem manuscriptHlift_eq : manuscriptHlift = 32099 := by
  unfold manuscriptHlift manuscriptCI manuscriptCloc manuscriptCrk
  rw [manuscriptCstep_eq]; norm_num

theorem manuscriptHlift_pos : 0 < manuscriptHlift := by
  rw [manuscriptHlift_eq]; norm_num

theorem manuscriptCdiamond_eq : manuscriptCdiamond = 2005 := by
  unfold manuscriptCdiamond manuscriptCloc manuscriptCsh manuscriptCAP
    manuscriptCres manuscriptCdp
  norm_num

theorem manuscriptCdiamond_pos : 0 < manuscriptCdiamond := by
  rw [manuscriptCdiamond_eq]; norm_num

theorem manuscriptPhand_eq : manuscriptPhand = 2182720 := by
  unfold manuscriptPhand
  rw [manuscriptHlift_eq, manuscriptCdiamond_eq]; norm_num

theorem manuscriptPhand_pos : 0 < manuscriptPhand := by
  rw [manuscriptPhand_eq]; norm_num

/-- **Convention 2.0′**: `0 < c_I ≤ C_step / 16`. -/
theorem manuscriptCI_le_Cstep_div_16 : manuscriptCI ≤ manuscriptCstep / 16 := by
  rw [manuscriptCstep_eq]; unfold manuscriptCI; norm_num

/-- **Convention 2.0a**: layer separation
`C_step − c_I ≥ 15 (C_loc + C_rk + C_sh + C_AP + C_res + C_dp + 1)`.
Equivalently `C_step − c_I = 32095 ≥ 30090`. -/
theorem manuscriptCstep_sub_cI_ge :
    15 * (manuscriptCloc + manuscriptCrk + manuscriptCsh + manuscriptCAP +
          manuscriptCres + manuscriptCdp + 1) ≤ manuscriptCstep - manuscriptCI := by
  unfold manuscriptCloc manuscriptCrk manuscriptCsh manuscriptCAP manuscriptCres
    manuscriptCdp manuscriptCI
  rw [manuscriptCstep_eq]; norm_num

/-- **Convention 2.0″**: `C_dp ≥ 4 + 2 c_Y⁻¹ (C_sh + C_AP + C_loc + 2 C_res)`.
At the pinned constants the floor is `4 + 327680/225 ≈ 1460.4 ≤ 2000`. -/
theorem manuscriptCdp_ge_floor :
    4 + 2 * (manuscriptCsh + manuscriptCAP + manuscriptCloc + 2 * manuscriptCres) /
        manuscriptCY ≤ manuscriptCdp := by
  unfold manuscriptCdp manuscriptCsh manuscriptCAP manuscriptCloc manuscriptCres
  rw [manuscriptCY_eq]; norm_num

/-! ### Bundle the pinned constants -/

/-- **Manuscript c₀** (Round Α2 manuscript-strict failure constant).
Pinned at `manuscriptKappa / 64`, which is well below `κ` and strictly below
`c_Q = 1/8`.  This is the failure threshold used in all quantitative manuscript
analysis.

The smaller pin matches the proof-v4 requirement `c₀ ≪ κ`, used by the carry
threshold budget in Lemma 21.1.
-/
def manuscriptC0 : ℝ := manuscriptKappa / 64

theorem manuscriptC0_pos : 0 < manuscriptC0 := by
  unfold manuscriptC0
  exact div_pos manuscriptKappa_pos (by norm_num)

theorem manuscriptC0_lt_kappa : manuscriptC0 < manuscriptKappa := by
  unfold manuscriptC0
  nlinarith [manuscriptKappa_pos]

theorem manuscriptC0_le_kappa_div_sixteen :
    manuscriptC0 ≤ manuscriptKappa / 16 := by
  unfold manuscriptC0
  nlinarith [manuscriptKappa_pos]

theorem manuscriptC0_le_cQ : manuscriptC0 ≤ manuscriptCQ := by
  have h_kappa_lt_eighth : manuscriptKappa < manuscriptCQ := by
    unfold manuscriptCQ
    have := manuscriptKappa_lt_one_sixteenth
    linarith
  have h_c0_lt_kappa : manuscriptC0 < manuscriptKappa := manuscriptC0_lt_kappa
  linarith

/-- The pinned manuscript constants packaged with their positivity and
the numerical compatibility used in `Erdos260AnalyticInputsAtomic`.

**Round Α2**: added strict failure constant `c0 ≤ cQ` with positivity. -/
structure Erdos260Constants where
  cQ : ℝ
  c0 : ℝ
  kappa : ℝ
  cPr : ℝ
  cStar : ℝ
  ξ : ℝ
  cQ_pos : 0 < cQ
  c0_pos : 0 < c0
  c0_le_cQ : c0 ≤ cQ
  kappa_pos : 0 < kappa
  c0_lt_kappa : c0 < kappa
  cPr_pos : 0 < cPr
  cStar_pos : 0 < cStar
  ξ_pos : 0 < ξ
  constantsCompatible : cStar * ξ < cPr

/-- The canonical concrete Pass-3 constants.  **Round Α2**: pinned
`c0 := manuscriptC0 = κ/64` and exposes the manuscript `κ` in the global
constant package. -/
def erdos260Constants : Erdos260Constants where
  cQ := manuscriptCQ
  c0 := manuscriptC0
  kappa := manuscriptKappa
  cPr := manuscriptCpr
  cStar := manuscriptCstar
  ξ := manuscriptXi
  cQ_pos := manuscriptCQ_pos
  c0_pos := manuscriptC0_pos
  c0_le_cQ := manuscriptC0_le_cQ
  kappa_pos := manuscriptKappa_pos
  c0_lt_kappa := manuscriptC0_lt_kappa
  cPr_pos := manuscriptCpr_pos
  cStar_pos := manuscriptCstar_pos
  ξ_pos := manuscriptXi_pos
  constantsCompatible := manuscript_constantsCompatible

theorem erdos260Constants_kappa_eq :
    erdos260Constants.kappa = manuscriptKappa := rfl

theorem erdos260Constants_c0_lt_kappa :
    erdos260Constants.c0 < erdos260Constants.kappa :=
  erdos260Constants.c0_lt_kappa

theorem erdos260Constants_kappa_eq_cdrop_c1_eps :
    erdos260Constants.kappa =
      manuscriptCdrop * manuscriptC1 * manuscriptEps := by
  rw [erdos260Constants_kappa_eq, manuscriptKappa_eq_cdrop_c1_eps]

end

end Erdos260
