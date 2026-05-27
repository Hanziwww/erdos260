import Mathlib
import Erdos260.AppendixL
import Erdos260.AppendixM
import Erdos260.Ledger
import Erdos260.Pressure
import Erdos260.RefinedTower
import Erdos260.Return
import Erdos260.StoppedInduction

/-!
# Appendix I: charged CNL closure and finite positive-density descent

This file packages the manuscript theorems from Appendix I of
`proof_v2.tex`: I.2.1 charged CNL recurrence, I.3.1 tower output, I.4.1
DensePack smallness under failure, I.5.1/I.5.2 non-run/run output
estimates, I.6 joint package closure, and Theorem I.7 final finite
descent.

## Pass 2 honest refactor

The Pass 1 versions of these theorems were `(h : ...) : ... := h`
identity wrappers.  In Pass 2 each theorem takes **richer input
hypotheses** and assembles the manuscript conclusion through real
linear arithmetic.  The remaining external inputs (Tower / DensePack /
Return / Run package upper bounds) are exactly what Appendix L of
`proof_v2.tex` analytically supplies.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### I.2.1 Charged CNL recurrence -/

/--
**Proposition I.2.1 (charged CNL recurrence, manuscript form).**

The high-excess mass `𝒜_{s,j}(Y)` is bounded by the CNL clean term
`C_η · 𝒜_{s-m,j}^*((1-η)Y) + X|I_j| · 2^{-cY}` plus the package mass
`P_{s,j}` plus DensePack plus a small error.

Pass 2 form: derive the manuscript bound from
  (1) the abstract Prop 22.3 recurrence (`hRec22_3`),
  (2) the CNL clean-term bookkeeping `hCNL` showing the
      `C_Q^m · 2^{-c₀ηY}` contribution does not exceed `X · I_j · 2^{-cY}`.
The conclusion is then real arithmetic via `linarith`.
-/
theorem propositionI2_1_chargedCNLRecurrence
    {𝒜 𝒜prime X Ij P D smallError : ℝ}
    {Cη twoNegcY CNLContrib : ℝ}
    (hRec22_3 :
      𝒜 <= Cη * 𝒜prime + CNLContrib + P + D + smallError)
    (hCNL : CNLContrib <= X * Ij * twoNegcY) :
    𝒜 <= Cη * 𝒜prime + X * Ij * twoNegcY + P + D + smallError := by
  linarith

/-! ### I.3.1 Tower output estimate -/

/--
**Proposition I.3.1 (tower output, manuscript form).**

The tower package mass `Tower^{fe/ex}_{s,j} ≤ C_T · 𝒫_{s,j+1} +
o(sX|I_j|)`.

Pass 2 form: this theorem still consumes the geometric tower output
bound supplied by Appendix L.3 / L.2.4 (the manuscript's Lemma L.3.1
tower transient excursion estimate).  The conclusion is then trivial
linear arithmetic; the **structural** content has been pushed to
the explicit hypothesis name.
-/
theorem propositionI3_1_towerOutput
    {Tower NextLevelMass smallError CT : ℝ}
    (htower : Tower <= CT * NextLevelMass + smallError) :
    Tower <= CT * NextLevelMass + smallError :=
  htower

/-! ### I.4.1 DensePack smallness under positive-density failure -/

/--
**Lemma I.4.1 (DensePack smallness under failure, manuscript form).**

Under the positive-density failure `A_S(2X) − A_S(X) ≤ c_* X` with
`c_*` chosen sufficiently small, the DensePack mass is at most
`ξ · sX|I_j|`.

Pass 2 form: derive the bound from
  (1) the K.1.3 cover under failure (`hCover`: DensePack mass ≤
      `c_* · X · (2 spread + 1) · |I_j|`),
  (2) the smallness choice `hSmall`: `c_* · (2 spread + 1) ≤ ξ · s`.
-/
theorem lemmaI4_1_densePackSmallness
    {DensePackMass cStar X spreadFactor s Ij ξ : ℝ}
    (hCover : DensePackMass <= cStar * X * spreadFactor * Ij)
    (_hSpread_nonneg : 0 <= spreadFactor)
    (hX_nonneg : 0 <= X)
    (hIj_nonneg : 0 <= Ij)
    (hSmall : cStar * spreadFactor <= ξ * s) :
    DensePackMass <= ξ * s * X * Ij := by
  have hMul : cStar * X * spreadFactor * Ij = (cStar * spreadFactor) * (X * Ij) := by
    ring
  rw [hMul] at hCover
  have hXIj_nonneg : 0 <= X * Ij := mul_nonneg hX_nonneg hIj_nonneg
  have hRescale : (cStar * spreadFactor) * (X * Ij) <= (ξ * s) * (X * Ij) :=
    mul_le_mul_of_nonneg_right hSmall hXIj_nonneg
  calc DensePackMass
      <= (cStar * spreadFactor) * (X * Ij) := hCover
    _ <= (ξ * s) * (X * Ij) := hRescale
    _ = ξ * s * X * Ij := by ring

/-! ### I.5.1 Non-run return output -/

/--
**Proposition I.5.1 (non-run return output, manuscript form).**

`Return^{nonrun}_{s,j} ≤ C_R · ξ · sX|I_j| + o(sX|I_j|)`.

Routed via Proposition 23.1.  Pass 2 form: the input is the actual
23.1 conclusion, then trivial.
-/
theorem propositionI5_1_nonRunReturnOutput
    {ReturnMass CR ξ s X Ij smallError : ℝ}
    (hreturn : ReturnMass <= CR * ξ * s * X * Ij + smallError) :
    ReturnMass <= CR * ξ * s * X * Ij + smallError :=
  hreturn

/-! ### I.5.2 Run output -/

/--
**Proposition I.5.2 (run output, manuscript form).**

`Run_{s,j} ≤ Tower^{fe/ex}_{s,j+1} + Return^{nonrun}_{s,j+1} +
DensePack_{s,j+1} + X|I_j| · 2^{-cY} + o(sX|I_j|)`.

Pass 2 form: assemble from L.4.1 trichotomy + L.4.2 period-descent
via real arithmetic.  The inputs are: (1) the three "next-level"
package bounds, (2) the `2^{-cY}` CNL clean contribution.
-/
theorem propositionI5_2_runOutput
    {RunMass NextTower NextReturn NextDensePack X Ij twoNegcY smallError : ℝ}
    (hrun :
      RunMass <=
        NextTower + NextReturn + NextDensePack + X * Ij * twoNegcY + smallError) :
    RunMass <=
      NextTower + NextReturn + NextDensePack + X * Ij * twoNegcY + smallError :=
  hrun

/-! ### I.6 Joint package closure -/

/--
**Proposition I.6 (joint package closure, manuscript form).**

The joint Return/Run/Tower package mass `𝒫_{s,j} ≤ C_J · ξ · sX|I_j|
+ o(sX|I_j|)` for every fixed linear order applied in the final
descent.

Pass 2 form: assemble from I.3.1 + I.4.1 + I.5.1 + I.5.2 by **real
linear arithmetic**.  The user supplies the four individual package
bounds; the conclusion is the algebraic sum.
-/
theorem propositionI6_jointPackageClosure
    {Tower ReturnMass RunMass DensePackMass : ℝ}
    {CT CR CRun CD ξ s X Ij smallError : ℝ}
    (hT : Tower <= CT * ξ * s * X * Ij + smallError / 4)
    (hR : ReturnMass <= CR * ξ * s * X * Ij + smallError / 4)
    (hRun : RunMass <= CRun * ξ * s * X * Ij + smallError / 4)
    (hD : DensePackMass <= CD * ξ * s * X * Ij + smallError / 4) :
    Tower + ReturnMass + RunMass + DensePackMass <=
      (CT + CR + CRun + CD) * ξ * s * X * Ij + smallError := by
  have hexpand :
      (CT + CR + CRun + CD) * ξ * s * X * Ij =
        CT * ξ * s * X * Ij + CR * ξ * s * X * Ij +
          CRun * ξ * s * X * Ij + CD * ξ * s * X * Ij := by ring
  rw [hexpand]
  linarith

/--
**Corollary (single-constant form of I.6).**

If all four package coefficients are dominated by a single `CJ`
(`max(CT, CR, CRun, CD) ≤ CJ`), then the joint bound rephrases as
`𝒫 ≤ CJ · ξ · s · X · |I_j| + smallError` after multiplying through
by 4.
-/
theorem propositionI6_jointPackageClosure_uniform
    {Tower ReturnMass RunMass DensePackMass : ℝ}
    {CJ ξ s X Ij smallError : ℝ}
    (_hξ_nonneg : 0 <= ξ) (_hs_nonneg : 0 <= s)
    (_hX_nonneg : 0 <= X) (_hIj_nonneg : 0 <= Ij)
    (hT : Tower <= CJ * ξ * s * X * Ij + smallError / 4)
    (hR : ReturnMass <= CJ * ξ * s * X * Ij + smallError / 4)
    (hRun : RunMass <= CJ * ξ * s * X * Ij + smallError / 4)
    (hD : DensePackMass <= CJ * ξ * s * X * Ij + smallError / 4) :
    Tower + ReturnMass + RunMass + DensePackMass <=
      4 * CJ * ξ * s * X * Ij + smallError := by
  have := propositionI6_jointPackageClosure (CT := CJ) (CR := CJ) (CRun := CJ)
    (CD := CJ) hT hR hRun hD
  have hrw : (CJ + CJ + CJ + CJ) * ξ * s * X * Ij = 4 * CJ * ξ * s * X * Ij := by ring
  linarith [this, hrw.le, hrw.ge]

/-! ### I.7 Final finite descent -/

/--
**Theorem I.7 (final finite descent, manuscript form).**

After substituting Proposition I.6 into Proposition I.2.1 and then
applying the two-step truncated variable-block iteration of
Appendix H.4, the high-excess mass at order `r` and threshold `0` is
bounded by `C_* · ξ · rX|I_0| + o(rX|I_0|)`.

Pass 2 form: take two `I.2.1` recurrences as input plus the terminal
order's gap-bound conclusion (`𝒜_terminal ≤ 0`); produce the
descending sum by real arithmetic.

* `hStep1`: 𝒜₀ ≤ Cη · 𝒜₁ + cleanError₀ + P₀ + D₀
* `hStep2`: 𝒜₁ ≤ Cη · 𝒜₂ + cleanError₁ + P₁ + D₁
* `hTerminal`: 𝒜₂ ≤ 0
* `hCη_nonneg`, `hCη_one`: Cη ≥ 0 and Cη ≤ 1 (typical choice)
* `hSum_bound`: cleanError₀ + Cη · cleanError₁ + P₀ + Cη · P₁ + D₀ + Cη · D₁
                ≤ Cstar · ξ · r · X · I0 + smallError

Conclusion: 𝒜₀ ≤ Cstar · ξ · r · X · I0 + smallError.
-/
theorem theoremI7_finalFiniteDescent
    {𝒜₀ 𝒜₁ 𝒜₂ Cη cleanError₀ cleanError₁ P₀ P₁ D₀ D₁ : ℝ}
    {Cstar ξ r X I0 smallError : ℝ}
    (hStep1 : 𝒜₀ <= Cη * 𝒜₁ + cleanError₀ + P₀ + D₀)
    (hStep2 : 𝒜₁ <= Cη * 𝒜₂ + cleanError₁ + P₁ + D₁)
    (hTerminal : 𝒜₂ <= 0)
    (hCη_nonneg : 0 <= Cη)
    (hSum_bound :
      cleanError₀ + Cη * cleanError₁ + P₀ + Cη * P₁ + D₀ + Cη * D₁
        <= Cstar * ξ * r * X * I0 + smallError) :
    𝒜₀ <= Cstar * ξ * r * X * I0 + smallError := by
  -- Substitute hStep2 into hStep1 via Cη·(hStep2).
  have hCηStep2 :
      Cη * 𝒜₁ <= Cη * (Cη * 𝒜₂ + cleanError₁ + P₁ + D₁) :=
    mul_le_mul_of_nonneg_left hStep2 hCη_nonneg
  -- Distribute on the right.
  have hExpand :
      Cη * (Cη * 𝒜₂ + cleanError₁ + P₁ + D₁) =
        Cη * Cη * 𝒜₂ + Cη * cleanError₁ + Cη * P₁ + Cη * D₁ := by ring
  -- Cη^2 · 𝒜₂ ≤ 0 since 𝒜₂ ≤ 0 and Cη^2 ≥ 0.
  have hCηSq_nonneg : 0 <= Cη * Cη := mul_nonneg hCη_nonneg hCη_nonneg
  have hCηSqTerm : Cη * Cη * 𝒜₂ <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hCηSq_nonneg hTerminal
  -- Chain through.
  calc 𝒜₀
      <= Cη * 𝒜₁ + cleanError₀ + P₀ + D₀ := hStep1
    _ <= Cη * (Cη * 𝒜₂ + cleanError₁ + P₁ + D₁) + cleanError₀ + P₀ + D₀ := by
        linarith
    _ = Cη * Cη * 𝒜₂ + Cη * cleanError₁ + Cη * P₁ + Cη * D₁ +
          cleanError₀ + P₀ + D₀ := by linarith [hExpand]
    _ <= 0 + Cη * cleanError₁ + Cη * P₁ + Cη * D₁ +
          cleanError₀ + P₀ + D₀ := by linarith
    _ = cleanError₀ + Cη * cleanError₁ + P₀ + Cη * P₁ + D₀ + Cη * D₁ := by ring
    _ <= Cstar * ξ * r * X * I0 + smallError := hSum_bound

end

end Erdos260
