import Mathlib
import Erdos260.Constants
import Erdos260.DirtyCrossing
import Erdos260.Lemma221Regular
import Erdos260.RunDescentConstruction

/-!
# Residual scalar / asymptotic budget inequalities (proof-v5 numeric residues)

Several primitives in the v5 development isolate their last obligation as a *pure
scalar inequality over the constant definitions* — not deep geometry.  This file
(new; it edits no existing file) discharges those tractable residues and isolates
the genuinely asymptotic ones behind an explicit, minimal regime hypothesis.

The four targets, with the manuscript section that pins each constant:

1. **Return `M_L` envelope budget** (`ReturnNestingConstruction.ReturnNestingCore.olc_ML_budget`,
   manuscript §J.4 / Cor. K.2.5):

   `M_L · X·|I_j| ≤ s · X·|I_j| / 2`,

   where `M_L = (log* L)^{C_M}·(log L)^4 = cleanedDirtyEnvelope`.  This is pure
   monotonicity once the **dirty multiplicity is below half the shell scale**,
   `M_L ≤ s/2`, the regime the manuscript records as `M_L = o(r)` (line 1614).  We
   prove the budget from that regime (`mL_budget_of_envelope_scale`) and package the
   manuscript's `M_L = o(r)` as a genuine `IsLittleO` ⟹ eventual-regime statement
   (`eventually_mL_budget_of_isLittleO`).

2. **Chernoff length calibration** (`Lemma221Regular.RegularStoppedChernoffFamily.calibration`,
   `ChernoffSubconjugacy.carryThresholdFibre_chernoffPhase`, manuscript §H.4 / §22.3):

   the admissible block length `m ≤ c₁·Y`.  This is a *definitional* relation
   between the H.4 two-step block length `m₁ = s₁ − 1` and the active floor
   `Y₁ = (1−η)εL`, holding from `C_drop ≤ 2−η`.  We prove it from the H.4
   definitions (`h4_m1_le_c1_Y1`, and the strict "large `L`" form
   `h4_m1_le_c1_Y1_of_large_L`), and supply the quantitative bridge that turns
   `m ≤ c₁Y` into the exact moment inequality the Chernoff family consumes
   (`calibration_moment_of_length` / `regularFamily_calibration_of_length`).

3. **Closure-vs-pressure constant condition**
   (`ChargeBridgeContradiction.highExcessMass_oldRes_contradiction`,
   manuscript Convention "order of quantifiers" §I.1 + recurrence I.11'):

   `cStar·ξ + C_Q·c_* < cPr`.  Given the older compatibility `cStar·ξ < cPr` and
   `C_Q > 0`, this holds for every `c_*` below the explicit threshold
   `c_* < (cPr − cStar·ξ)/C_Q` (`closure_pressure_of_cStarSmall_lt`); a witness is
   exhibited (`exists_cStarSmall_closure_pressure`), encoding "choose `c_*` last".
   We instantiate it at the pinned manuscript constants for any `0 ≤ C_Q ≤ 1`
   (`manuscript_closure_pressure_le_one`), in particular the conservative cluster
   value `C_Q = 1` and the positive-density constant `C_Q = c_Q = 1/8`.

4. **Run chain absorption** (`RunDescentConstruction.RunFamilyCore.ofDescentAndRouting`,
   manuscript §L.4.2):

   the `chain_capture` + `chainRoot_le` routing input.  Chaining the proved L.4.2
   descent-potential bound `∑ wt(O_i) ≤ 2·wt(O_0)` (`RunPeriodDescentChain.descent_sum`)
   with the two structure inputs collapses to the pure inequality
   `chainMass ≤ X·|I_j|·2^{−c_Y}` (`runChainMass_le_budget`); the residual
   `chainRoot_le` reduces to the initial-period bound `wt(O_0) ≤ X·|I_j|·2^{−c_Y}/2`
   (`chainRoot_le_of_initial_period_le`).

No `sorry`, `axiom`, or `admit`.  Every inequality is either proved outright from
the constant definitions, or proved under an explicit minimal regime hypothesis
that is stated as a hypothesis.
-/

namespace Erdos260

open Finset
open Asymptotics Filter

noncomputable section

/-! ## Target 1 — Return `M_L` envelope budget `M_L·X·|I_j| ≤ s·X·|I_j|/2`

The field `ReturnNestingCore.olc_ML_budget` asks for `(M_L : ℝ)·X·|I_j| ≤ s·X·|I_j|/2`
where `M_L = (log* L)^{C_M}·(log L)^4`.  This is pure monotonicity: once the dirty
multiplicity is below half the shell scale (`M_L ≤ s/2`), multiplying by the
nonnegative area `X·|I_j|` gives the budget.  The regime `M_L ≤ s/2` is the
manuscript's `M_L = o(r)` (the `M_L`-loss is confined to the Return estimate). -/

/--
**Half-scale budget (pure monotonicity).**  If a value `mlVal` is at most half a
scale `s`, then `mlVal·X·|I_j| ≤ s·X·|I_j|/2` for any nonnegative area `X·|I_j|`.
This is the algebraic core of the `olc_ML_budget` field. -/
theorem mul_two_budget_of_le_half {mlVal X ij s : ℝ}
    (hreg : mlVal ≤ s / 2) (hXij : 0 ≤ X * ij) :
    mlVal * X * ij ≤ s * X * ij / 2 := by
  calc mlVal * X * ij = mlVal * (X * ij) := by ring
    _ ≤ (s / 2) * (X * ij) := mul_le_mul_of_nonneg_right hreg hXij
    _ = s * X * ij / 2 := by ring

/--
**Target 1 (Return `M_L` envelope budget, from the scale regime).**

`M_L·X·|I_j| ≤ s·X·|I_j|/2` for a `Nat` dirty multiplicity `M_L`, under the regime
hypothesis `M_L ≤ s/2` (the manuscript's `M_L = o(r)` confined to the Return
estimate) and the area nonnegativity `0 ≤ X·|I_j|`.  This is exactly the shape of
`ReturnNestingCore.olc_ML_budget`. -/
theorem mL_budget_of_scale {ML : ℕ} {X ij s : ℝ}
    (hreg : (ML : ℝ) ≤ s / 2) (hXij : 0 ≤ X * ij) :
    (ML : ℝ) * X * ij ≤ s * X * ij / 2 :=
  mul_two_budget_of_le_half hreg hXij

/--
**Target 1 with the genuine envelope `M_L = (log* L)^{C_M}·(log L)^4`.**

The budget for the concrete `cleanedDirtyEnvelope` (Cor. K.2.5), under the regime
`2·M_L ≤ s` (i.e. the shell scale is at least twice the dirty multiplicity). -/
theorem mL_budget_of_envelope_scale
    {logStar : ℕ → ℕ} {CM L : ℕ} {X ij s : ℝ}
    (hreg : 2 * (cleanedDirtyEnvelope logStar CM L : ℝ) ≤ s)
    (hXij : 0 ≤ X * ij) :
    (cleanedDirtyEnvelope logStar CM L : ℝ) * X * ij ≤ s * X * ij / 2 :=
  mL_budget_of_scale (by linarith) hXij

/--
**`M_L = o(s)` ⟹ eventual half-scale regime.**

The honest asymptotic packaging of the regime hypothesis: if the dirty
multiplicity `mL` is little-o of the scale `sScale` (both eventually nonnegative),
then eventually `mL ≤ sScale/2`.  This is the manuscript's `M_L = o(r)` made into
the regime `2·M_L ≤ s` consumed by Target 1. -/
theorem eventually_le_half_of_isLittleO
    {mL sScale : ℕ → ℝ}
    (hmL : ∀ᶠ L in atTop, 0 ≤ mL L)
    (hs : ∀ᶠ L in atTop, 0 ≤ sScale L)
    (hlittleO : (fun L => mL L) =o[atTop] fun L => sScale L) :
    ∀ᶠ L in atTop, mL L ≤ sScale L / 2 := by
  have hc : ∀ᶠ L in atTop, ‖mL L‖ ≤ (1 / 2 : ℝ) * ‖sScale L‖ :=
    (Asymptotics.isLittleO_iff.mp hlittleO) (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hc, hmL, hs] with L hL hmLnn hsnn
  rw [Real.norm_of_nonneg hmLnn, Real.norm_of_nonneg hsnn] at hL
  linarith

/--
**Target 1, asymptotic form.**  If `M_L = o(s)`, then the envelope budget
`M_L·X·|I_j| ≤ s·X·|I_j|/2` holds for all sufficiently large `L`. -/
theorem eventually_mL_budget_of_isLittleO
    {mL sScale : ℕ → ℝ} {X ij : ℝ} (hXij : 0 ≤ X * ij)
    (hmL : ∀ᶠ L in atTop, 0 ≤ mL L)
    (hs : ∀ᶠ L in atTop, 0 ≤ sScale L)
    (hlittleO : (fun L => mL L) =o[atTop] fun L => sScale L) :
    ∀ᶠ L in atTop, mL L * X * ij ≤ sScale L * X * ij / 2 := by
  filter_upwards [eventually_le_half_of_isLittleO hmL hs hlittleO] with L hL
  exact mul_two_budget_of_le_half hL hXij

/-! ## Target 2 — Chernoff length calibration `m ≤ c₁·Y`

The manuscript §H.4 two-step truncated iteration sets (lines 2423–2452):

```
Y₁ = (1 − η)·ε·L,   s₁ = (C_drop − 1)·c₁·ε·L + O(1),   m₁ = s₁ − 1,
```

and concludes `m₁ ≤ c₁·Y₁` from `C_drop < 2 − η` ("for all sufficiently large L").
We model `Y₁`, `s₁`, `m₁` as real functions of `L`, with the `O(1)` term an explicit
error `err`, and prove the calibration from the H.4 chain `C_drop − 1 ≤ 1 − η`. -/

/-- Manuscript H.4 active floor `Y₁ = (1 − η)·ε·L`. -/
def h4Y1 (η ε L : ℝ) : ℝ := (1 - η) * ε * L

/-- Manuscript H.4 second shell scale `s₁ = (C_drop − 1)·c₁·ε·L + err` (`err = O(1)`). -/
def h4s1 (Cdrop c1 ε L err : ℝ) : ℝ := (Cdrop - 1) * c1 * ε * L + err

/-- Manuscript H.4 truncated final block length `m₁ = s₁ − 1`. -/
def h4m1 (Cdrop c1 ε L err : ℝ) : ℝ := h4s1 Cdrop c1 ε L err - 1

/--
**Target 2 (H.4 length calibration `m₁ ≤ c₁·Y₁`, clean form).**

From the H.4 chain `C_drop − 1 ≤ 1 − η` (equivalently `C_drop ≤ 2 − η`), the
nonnegativity `0 ≤ c₁·ε·L`, and a bounded `O(1)` error `err ≤ 1`, the truncated
final block is admissible: `m₁ ≤ c₁·Y₁`.

The mechanism is exactly the manuscript's: the linear coefficient comparison
`(C_drop − 1) ≤ (1 − η)` makes `s₁` undershoot `c₁·Y₁ + (1 + (err−1))`, and the
`−1` of `m₁ = s₁ − 1` absorbs the harmless `err ≤ 1`. -/
theorem h4m1_le_c1_Y1
    {Cdrop η ε c1 L err : ℝ}
    (hchain : Cdrop - 1 ≤ 1 - η)
    (hprod : 0 ≤ c1 * ε * L)
    (herr : err ≤ 1) :
    h4m1 Cdrop c1 ε L err ≤ c1 * h4Y1 η ε L := by
  unfold h4m1 h4s1 h4Y1
  have hgap : 0 ≤ c1 * ε * L * ((1 - η) - (Cdrop - 1)) :=
    mul_nonneg hprod (by linarith)
  nlinarith [hgap, herr]

/--
**Target 2 (H.4 length calibration, strict "large `L`" form).**

The genuinely asymptotic version: when `C_drop < 2 − η` *strictly* (positive gap
`(2 − η) − C_drop`) and `err ≤ Cerr` for an arbitrary `O(1)` bound, the calibration
`m₁ ≤ c₁·Y₁` holds once `L` clears the explicit threshold
`Cerr − 1 ≤ c₁·((2 − η) − C_drop)·ε·L`, i.e. `L ≥ (Cerr − 1)/(c₁·((2 − η) − C_drop)·ε)`. -/
theorem h4m1_le_c1_Y1_of_large_L
    {Cdrop η ε c1 L err Cerr : ℝ}
    (herr : err ≤ Cerr)
    (hL : Cerr - 1 ≤ c1 * ε * L * ((1 - η) - (Cdrop - 1))) :
    h4m1 Cdrop c1 ε L err ≤ c1 * h4Y1 η ε L := by
  unfold h4m1 h4s1 h4Y1
  nlinarith [hL, herr]

/--
**Manuscript-pinned H.4 calibration.**

At the pinned `C_drop = 17/16`, `η = 1/16`, the H.4 chain `C_drop − 1 ≤ 1 − η`
holds, so for any `0 ≤ c₁·ε·L` and `err ≤ 1` the calibration `m₁ ≤ c₁·Y₁` holds.
(`manuscriptCdrop_lt_two_sub_eta` is the strict source.) -/
theorem manuscript_h4m1_le_c1_Y1
    {ε c1 L err : ℝ} (hprod : 0 ≤ c1 * ε * L) (herr : err ≤ 1) :
    h4m1 manuscriptCdrop c1 ε L err ≤ c1 * h4Y1 manuscriptEta ε L := by
  refine h4m1_le_c1_Y1 ?_ hprod herr
  have := manuscriptCdrop_lt_two_sub_eta
  linarith

/-! ### Quantitative bridge: `m ≤ c₁Y` ⟹ the moment fits the budget

The Chernoff family field `RegularStoppedChernoffFamily.calibration` is the
*quantitative* form

`rootMass · (K·tiltSum)^m ≤ (cStar·ξ·X/6) · z^Y`.

The manuscript turns the length bound `m ≤ c₁Y` into this by "choosing `c₁`
sufficiently small" (lines 877–879).  Concretely: if one regular edge costs at
most `d` threshold units of base `z` (`K·tiltSum ≤ z^d`) and the calibration reads
`d·m ≤ Y` (i.e. `m ≤ Y/d`, so `c₁ = 1/d`), and `rootMass ≤ budget`, then the moment
undershoots the budget.  Pure power monotonicity. -/

/--
**Calibration bridge (pure scalar).**  With base `z ≥ 1`, nonnegative `rootMass`,
nonnegative per-path base `B`, `rootMass ≤ budget`, per-edge bound `B ≤ z^d`, and
the length calibration `d·m ≤ Y` (the `m ≤ c₁Y` of §22.3 with `c₁ = 1/d`):

`rootMass · B^m ≤ budget · z^Y`. -/
theorem calibration_moment_of_length
    {rootMass budget B z : ℝ} {d m Y : ℕ}
    (hz : 1 ≤ z) (hroot_nonneg : 0 ≤ rootMass) (hB_nonneg : 0 ≤ B)
    (hroot_le : rootMass ≤ budget)
    (hB_le : B ≤ z ^ d)
    (hcal : d * m ≤ Y) :
    rootMass * B ^ m ≤ budget * z ^ Y := by
  have hbudget_nonneg : 0 ≤ budget := le_trans hroot_nonneg hroot_le
  have hBm_le_zdm : B ^ m ≤ z ^ (d * m) := by
    calc B ^ m ≤ (z ^ d) ^ m := pow_le_pow_left₀ hB_nonneg hB_le m
      _ = z ^ (d * m) := (pow_mul z d m).symm
  have hzdm_le_zY : z ^ (d * m) ≤ z ^ Y := pow_le_pow_right₀ hz hcal
  have hBm_le : B ^ m ≤ z ^ Y := le_trans hBm_le_zdm hzdm_le_zY
  have hBm_nonneg : 0 ≤ B ^ m := pow_nonneg hB_nonneg m
  calc rootMass * B ^ m
      ≤ budget * B ^ m := mul_le_mul_of_nonneg_right hroot_le hBm_nonneg
    _ ≤ budget * z ^ Y := mul_le_mul_of_nonneg_left hBm_le hbudget_nonneg

/--
**Target 2 capstone — the exact `RegularStoppedChernoffFamily.calibration` field.**

Specializing `calibration_moment_of_length` with `B := K·regularTiltSum Csh G z`
and `budget := cStar·ξ·X/6` yields precisely the type of the `calibration` field of
`RegularStoppedChernoffFamily` (and of the `calibration` hypothesis of
`ChernoffSubconjugacy.carryThresholdFibre_chernoffPhase`).  So the length
calibration `d·m ≤ Y` plus the regular-tilt convergence bound `K·tiltSum ≤ z^d`
discharge the Chernoff phase's numeric input. -/
theorem regularFamily_calibration_of_length
    {Csh G m Y d : ℕ} {cStar ξ X rootMass K z : ℝ}
    (hz : 1 ≤ z)
    (hroot_nonneg : 0 ≤ rootMass)
    (hKtilt_nonneg : 0 ≤ K * regularTiltSum Csh G z)
    (hroot_le : rootMass ≤ cStar * ξ * X / 6)
    (hKtilt_le : K * regularTiltSum Csh G z ≤ z ^ d)
    (hcal : d * m ≤ Y) :
    rootMass * (K * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y :=
  calibration_moment_of_length hz hroot_nonneg hKtilt_nonneg hroot_le hKtilt_le hcal

/-! ## Target 3 — closure-vs-pressure constant condition `cStar·ξ + C_Q·c_* < cPr`

The v5 contradiction engine `highExcessMass_oldRes_contradiction` requires the
augmented constant condition `cStar·ξ + C_Q·c_* < cPr` (the analog of the old
`cStar·ξ < cPr`, now absorbing the old-residual constant `C_Q·c_*`).  By the
manuscript Convention on the order of quantifiers (§I.1), `c_*` is chosen **last**,
after `cStar`, `ξ`, `C_Q`, `cPr`; so the condition is satisfiable by taking `c_*`
small.  The explicit smallness threshold is `c_* < (cPr − cStar·ξ)/C_Q`. -/

/--
**Target 3 (closure-vs-pressure, from raw smallness).**  If `C_Q·c_*` is strictly
below the slack `cPr − cStar·ξ`, then `cStar·ξ + C_Q·c_* < cPr`.  (Pure linear
arithmetic; the conclusion is exactly the `hcompat` input of
`highExcessMass_oldRes_contradiction`.) -/
theorem closure_pressure_of_slack
    {cStar ξ cQ cStarSmall cPr : ℝ}
    (hsmall : cQ * cStarSmall < cPr - cStar * ξ) :
    cStar * ξ + cQ * cStarSmall < cPr := by
  linarith

/--
**Target 3 (closure-vs-pressure, explicit smallness on `c_*`).**

Given the older numerical compatibility `cStar·ξ < cPr` and a positive old-residual
constant `C_Q > 0`, the augmented condition `cStar·ξ + C_Q·c_* < cPr` holds for
every `c_*` below the explicit threshold `c_* < (cPr − cStar·ξ)/C_Q`.  This is the
faithful "choose `c_*` last, small enough" of Convention §I.1. -/
theorem closure_pressure_of_cStarSmall_lt
    {cStar ξ cQ cStarSmall cPr : ℝ}
    (hcQ : 0 < cQ)
    (hsmall : cStarSmall < (cPr - cStar * ξ) / cQ) :
    cStar * ξ + cQ * cStarSmall < cPr := by
  rw [lt_div_iff₀ hcQ] at hsmall
  rw [mul_comm cQ cStarSmall]
  linarith

/--
**Target 3 (existence of a working `c_*`).**

If `cStar·ξ < cPr` and `C_Q > 0`, there is a *positive* `c_*` making
`cStar·ξ + C_Q·c_* < cPr`.  The witness `c_* := (cPr − cStar·ξ)/(2·C_Q)` is the
explicit "last constant" of the I.1 order of quantifiers. -/
theorem exists_cStarSmall_closure_pressure
    {cStar ξ cQ cPr : ℝ} (hcQ : 0 < cQ) (hcompat : cStar * ξ < cPr) :
    ∃ cStarSmall : ℝ, 0 < cStarSmall ∧ cStar * ξ + cQ * cStarSmall < cPr := by
  have hslack : 0 < cPr - cStar * ξ := by linarith
  refine ⟨(cPr - cStar * ξ) / (2 * cQ), by positivity, ?_⟩
  have h2cQ : 0 < 2 * cQ := by linarith
  have hval : cQ * ((cPr - cStar * ξ) / (2 * cQ)) = (cPr - cStar * ξ) / 2 := by
    field_simp
  rw [hval]
  linarith

/--
**Target 3, pinned at the manuscript constants for any `0 ≤ C_Q ≤ 1`.**

At the pinned values `cStar = 31/16`, `ξ = 1/16`, `cPr = 1/2`, and the failure
constant `c_* = manuscriptCstarSmall = κ·ξ/64`, the augmented condition holds for
every old-residual constant `0 ≤ C_Q ≤ 1`:

`cStar·ξ + C_Q·c_* ≤ 31/256 + c_* < 31/256 + 1/128 = 33/256 < 1/2 = cPr`.

In particular it covers the conservative cluster value `C_Q = 1` and the
positive-density constant `C_Q = c_Q = 1/8`. -/
theorem manuscript_closure_pressure_le_one
    {cQ : ℝ} (_hcQ_nonneg : 0 ≤ cQ) (hcQ_le : cQ ≤ 1) :
    manuscriptCstar * manuscriptXi + cQ * manuscriptCstarSmall < manuscriptCpr := by
  have hsmall_pos : 0 < manuscriptCstarSmall := manuscriptCstarSmall_pos
  have hcQc : cQ * manuscriptCstarSmall ≤ manuscriptCstarSmall := by
    calc cQ * manuscriptCstarSmall ≤ 1 * manuscriptCstarSmall :=
          mul_le_mul_of_nonneg_right hcQ_le hsmall_pos.le
      _ = manuscriptCstarSmall := one_mul _
  have hxi : manuscriptCstar * manuscriptXi = 31 / 256 := manuscriptCstar_mul_xi_eq_31_256
  have hsmall_lt : manuscriptCstarSmall < manuscriptXi / 8 :=
    manuscriptCstarSmall_lt_xi_div_eight
  have hxi8 : manuscriptXi / 8 = 1 / 128 := by unfold manuscriptXi; norm_num
  have hcpr : manuscriptCpr = 1 / 2 := manuscriptCpr_eq_half
  rw [hxi, hcpr]
  rw [hxi8] at hsmall_lt
  linarith

/--
**Target 3, the conservative-cluster instance `C_Q = 1`.**

The augmented closure-vs-pressure condition at the pinned manuscript constants with
the conservative cluster old-residual constant `C_Q = 1`. -/
theorem manuscript_closure_pressure :
    manuscriptCstar * manuscriptXi + 1 * manuscriptCstarSmall < manuscriptCpr :=
  manuscript_closure_pressure_le_one (by norm_num) (le_refl _)

/-! ## Target 4 — Run chain absorption `chainMass ≤ X·|I_j|·2^{−c_Y}`

`RunFamilyCore.ofDescentAndRouting` takes two Run-chain inputs:

* `chain_capture : chainMass ≤ ∑_{i<len} wt(O_i)`, and
* `chainRoot_le  : 2·wt(O_0) ≤ X·|I_j|·2^{−c_Y}`.

The proved L.4.2 descent-potential bound `∑_{i<len} wt(O_i) ≤ 2·wt(O_0)`
(`RunPeriodDescentChain.descent_sum`) chains these into a single pure inequality
`chainMass ≤ X·|I_j|·2^{−c_Y}` — the genuine routing input. -/

/--
**Target 4 (Run chain absorption, pure inequality).**

For a proved L.4.2 descent chain `C` (every step halving the run period), the
`chain_capture` bound `chainMass ≤ ∑_{i<len} wt(O_i)` and the `chainRoot_le` budget
`2·wt(O_0) ≤ budget` give `chainMass ≤ budget`, via the descent-potential bound
`∑_{i<len} wt(O_i) ≤ 2·wt(O_0)`.  With `budget = X·|I_j|·2^{−c_Y}` this is precisely
the Run-chain routing absorption. -/
theorem runChainMass_le_budget
    (C : RunPeriodDescentChain) (len : ℕ)
    {chainMass budget : ℝ}
    (hcapture : chainMass ≤ ∑ i ∈ Finset.range len, (C.period i : ℝ))
    (hchainRoot : 2 * (C.period 0 : ℝ) ≤ budget) :
    chainMass ≤ budget := by
  have hdesc : ∑ i ∈ Finset.range len, (C.period i : ℝ) ≤ 2 * (C.period 0 : ℝ) :=
    C.descent_sum len
  linarith

/--
**Target 4 (`chainRoot_le` from the initial-period bound).**

The `chainRoot_le` field `2·wt(O_0) ≤ budget` is the doubling of the initial-period
routing bound `wt(O_0) ≤ budget/2` — the counting statement that the root run period
fits half the shell budget `X·|I_j|·2^{−c_Y}`. -/
theorem chainRoot_le_of_initial_period_le
    (C : RunPeriodDescentChain) {budget : ℝ}
    (h : (C.period 0 : ℝ) ≤ budget / 2) :
    2 * (C.period 0 : ℝ) ≤ budget := by
  linarith

/--
**Target 4, fully assembled.**  From the descent chain, the `chain_capture` bound,
and the initial-period routing bound `wt(O_0) ≤ X·|I_j|·2^{−c_Y}/2`, the chain mass
is absorbed: `chainMass ≤ X·|I_j|·2^{−c_Y}`. -/
theorem runChainMass_le_of_initial_period_le
    (C : RunPeriodDescentChain) (len : ℕ)
    {chainMass X Ij twoNegcY : ℝ}
    (hcapture : chainMass ≤ ∑ i ∈ Finset.range len, (C.period i : ℝ))
    (hinit : (C.period 0 : ℝ) ≤ X * Ij * twoNegcY / 2) :
    chainMass ≤ X * Ij * twoNegcY :=
  runChainMass_le_budget C len hcapture (chainRoot_le_of_initial_period_le C hinit)

/-! ## Honest per-target status inventory -/

/-- Per-target honesty report: what is proved outright vs under an explicit regime. -/
def residualScalarBudgetStatus : List String :=
  [ "Target 1 (Return M_L envelope M_L·X|I_j| ≤ s·X|I_j|/2): PROVED under the " ++
      "explicit regime 2·M_L ≤ s (manuscript M_L = o(r)); the regime itself is " ++
      "the eventual consequence of M_L =o[atTop] s (eventually_mL_budget_of_isLittleO).",
    "Target 2 (Chernoff length calibration m ≤ c₁Y): PROVED from the §H.4 block " ++
      "definitions under C_drop ≤ 2−η plus err ≤ 1 (h4m1_le_c1_Y1); strict large-L " ++
      "form h4m1_le_c1_Y1_of_large_L. Quantitative moment bridge to the " ++
      "RegularStoppedChernoffFamily.calibration field PROVED (calibration_moment_of_length).",
    "Target 3 (cStar·ξ + C_Q·c_* < cPr): PROVED for every c_* below the explicit " ++
      "threshold (cPr−cStar·ξ)/C_Q (closure_pressure_of_cStarSmall_lt); witness " ++
      "exhibited; pinned manuscript instance for all 0 ≤ C_Q ≤ 1 (manuscript_closure_pressure_le_one).",
    "Target 4 (Run chain absorption chainMass ≤ X|I_j|·2^{−c_Y}): PROVED from the " ++
      "L.4.2 descent-potential bound + chain_capture + chainRoot_le (runChainMass_le_budget); " ++
      "chainRoot_le reduced to the initial-period routing bound." ]

theorem residualScalarBudgetStatus_nonempty : residualScalarBudgetStatus ≠ [] := by
  simp [residualScalarBudgetStatus]

end

end Erdos260
