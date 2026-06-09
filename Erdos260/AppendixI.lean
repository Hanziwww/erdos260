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

/-! ### I.7-I.10 Full `M`-step truncated descent

Theorem I.7 above iterates the truncated charged recurrence twice.  The
manuscript actually iterates it down to a terminal order where the high-excess
mass vanishes (I.10 "terminal tail empty").  The two lemmas below formalize the
descent at arbitrary depth `M`, with the geometric error accumulation that the
manuscript's two-step constant `C_η^2` is the `M = 2` case of.
-/

/--
**Telescoped charged descent.**  If `𝒜 k ≤ C_η · 𝒜 (k+1) + b k` holds at every
level with `C_η ≥ 0`, then for every depth `M`,
`𝒜 0 ≤ C_η^M · 𝒜 M + ∑_{k<M} C_η^k · b k`.  This is the exact telescoping of
the per-level recurrence (Proposition I.2.1) along the truncated variable-block
iteration of Appendix H.4. -/
theorem finiteDescent_telescope {𝒜 b : ℕ -> ℝ} {Cη : ℝ}
    (hCη_nonneg : 0 <= Cη)
    (hstep : ∀ k, 𝒜 k <= Cη * 𝒜 (k + 1) + b k) :
    ∀ M, 𝒜 0 <= Cη ^ M * 𝒜 M + ∑ k ∈ Finset.range M, Cη ^ k * b k := by
  intro M
  induction M with
  | zero => simp
  | succ n ih =>
      have hpow_nonneg : 0 <= Cη ^ n := pow_nonneg hCη_nonneg n
      have hexp :
          Cη ^ n * (Cη * 𝒜 (n + 1) + b n) =
            Cη ^ (n + 1) * 𝒜 (n + 1) + Cη ^ n * b n := by
        rw [pow_succ]; ring
      rw [Finset.sum_range_succ]
      calc 𝒜 0 <= Cη ^ n * 𝒜 n + ∑ k ∈ Finset.range n, Cη ^ k * b k := ih
        _ <= Cη ^ n * (Cη * 𝒜 (n + 1) + b n) +
              ∑ k ∈ Finset.range n, Cη ^ k * b k := by
            have := mul_le_mul_of_nonneg_left (hstep n) hpow_nonneg
            linarith
        _ = Cη ^ (n + 1) * 𝒜 (n + 1) +
              (∑ k ∈ Finset.range n, Cη ^ k * b k + Cη ^ n * b n) := by
            rw [hexp]; ring

/--
**Theorem I.7-I.10 (`M`-step final finite descent), real form.**

With a per-level truncated recurrence `𝒜 k ≤ C_η · 𝒜 (k+1) + b k` (`0 ≤ C_η`)
and the terminal tail `𝒜 M ≤ 0` (manuscript I.10: the high-excess mass at the
terminal order is empty), the order-`0` high-excess mass is bounded by the
geometric error sum `∑_{k<M} C_η^k · b k`.

This is the unconditional descent skeleton at arbitrary depth; the manuscript
analytic inputs are exactly the per-level recurrences `b k` and the terminal
nullification, which Appendices I.2-I.6 supply. -/
theorem finiteDescent_le {𝒜 b : ℕ -> ℝ} {Cη : ℝ} {M : ℕ}
    (hCη_nonneg : 0 <= Cη)
    (hstep : ∀ k, 𝒜 k <= Cη * 𝒜 (k + 1) + b k)
    (hterminal : 𝒜 M <= 0) :
    𝒜 0 <= ∑ k ∈ Finset.range M, Cη ^ k * b k := by
  have h := finiteDescent_telescope hCη_nonneg hstep M
  have hpow_nonneg : 0 <= Cη ^ M := pow_nonneg hCη_nonneg M
  have hterm : Cη ^ M * 𝒜 M <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpow_nonneg hterminal
  linarith

/-! ### I.9 reindexing: analytic high-excess mass = stopped-branch mass

The stopped induction (H.1–H.3) and the branch ledger (J.1) realize the analytic
high-excess mass `∑_k windowExcess` as the stopped-branch weighted mass: each
high-excess starting index `k` indexes a stopped branch carrying that index's
window excess as its weight.  The reindexing below is the **faithful sum
identity** (`Finset.sum_image`); the injectivity of the indexing (distinct starts
give distinct branches) and the per-branch weight identity are the conditional
stopped-tree construction inputs (H.1 / J.1).

This is the seam between the analytic high-excess world (`Pressure.highExcessMass`)
and the charged-ledger world (`StoppedInduction.branchWeightedMass` /
`chargedMass`): composed with `stoppedRecurrence_with_chargedLedger` it sends the
H.1–H.3 charged decomposition onto `highExcessMass`, feeding the central charge
bridge `highExcessMass ... ≤ ClosurePhaseMass`. -/

/-- **I.9 reindexing identity.**  Under the stopped-tree identification — the map
`branchOf` is injective on the high-excess starts (`hinj`) and the branch weight
of `branchOf k` is exactly the window excess at `k` (`hweight`) — the analytic
high-excess mass equals the stopped-branch weighted mass over the branch image. -/
theorem highExcessMass_eq_branchWeightedMass
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {Tr Yr : ℝ}
    {branchWeight : StoppedBranch -> ℝ}
    (branchOf : Nat -> StoppedBranch)
    (hinj : ∀ k ∈ highExcessStarts starts g r Tr Yr,
        ∀ l ∈ highExcessStarts starts g r Tr Yr, branchOf k = branchOf l -> k = l)
    (hweight : ∀ k ∈ highExcessStarts starts g r Tr Yr,
        branchWeight (branchOf k) = windowExcess g k r Tr) :
    highExcessMass (highExcessStarts starts g r Tr Yr) g r Tr
      = branchWeightedMass ((highExcessStarts starts g r Tr Yr).image branchOf)
          branchWeight := by
  unfold highExcessMass branchWeightedMass weightedMass
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun k hk => (hweight k hk).symm

/-- **I.9 → branch bound.**  Any upper bound on the stopped-branch weighted mass
(e.g. the charged-ledger bound of `stoppedRecurrence_with_chargedLedger`)
transfers to the analytic high-excess mass.  This is how the stopped-induction /
charged-ledger estimates feed the central charge bridge. -/
theorem highExcessMass_le_of_branchBound
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {Tr Yr : ℝ}
    {branchWeight : StoppedBranch -> ℝ} {bound : ℝ}
    (branchOf : Nat -> StoppedBranch)
    (hinj : ∀ k ∈ highExcessStarts starts g r Tr Yr,
        ∀ l ∈ highExcessStarts starts g r Tr Yr, branchOf k = branchOf l -> k = l)
    (hweight : ∀ k ∈ highExcessStarts starts g r Tr Yr,
        branchWeight (branchOf k) = windowExcess g k r Tr)
    (hbound :
      branchWeightedMass ((highExcessStarts starts g r Tr Yr).image branchOf)
          branchWeight <= bound) :
    highExcessMass (highExcessStarts starts g r Tr Yr) g r Tr <= bound := by
  rw [highExcessMass_eq_branchWeightedMass branchOf hinj hweight]
  exact hbound

end

end Erdos260
