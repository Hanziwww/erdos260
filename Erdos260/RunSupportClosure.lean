import Erdos260.RunResidualClosure

/-!
# Run support closure: product form of the Section 26 support residual

This module does not fake the remaining Run/Class 5 residual with a canonical
stage map. The I.6S map and the finite L.4.2 half-decrease remain genuine
analytic inputs.

What it does sharpen is the support side of `RunClass5LeafSupportResidual`.
The explicit `rhoL` witness, packing, and K.4 smallness are converted to and
from one support-relative product inequality, together with the necessary
nondegeneracy that the shell support is positive when the base fibre is
nonempty.

No `sorry`, `axiom`, `admit`, `native_decide`, or empty/vacuous stage-map
witness is introduced.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The actual failure context has nonempty shell support in the dyadic window. -/
theorem actualFailureContext_supportShell_card_pos (ctx : ActualFailureContext) :
    0 < ((supportShell ctx.d ctx.X).card : Real) := by
  have hlt : ctx.n24CarryLocal.r < (supportShell ctx.d ctx.X).card := by
    simpa [ActualFailureContext.shell_X] using ctx.n24CarryLocal.hKr
  exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hlt)

/-- Product-form support residual for the Run class-5 leaf. -/
structure RunClass5LeafSupportProductResidual (ctx : ActualFailureContext) where
  /-- The I.6S charge/stage map of the class-5 fibre. -/
  stageOf : Nat -> Nat
  /-- The finite L.4.2 mass half-decrease on genuine within-descent steps. -/
  hhalf : forall i, i + 1 < runStageLen ctx stageOf ->
    stageMassOf ctx stageOf (i + 1) <= (1 / 2) * stageMassOf ctx stageOf i
  /-- Nondegeneracy needed to select a positive per-hit floor. -/
  hsupport_nontrivial :
    (runBaseFibre ctx stageOf).card = 0 \/
      0 < ((supportShell ctx.d ctx.X).card : Real)
  /-- The support-relative Section 26 product bound. -/
  hproduct :
    erdos260Constants.c0 * ((runBaseFibre ctx stageOf).card : Real) *
        stageMassOf ctx stageOf 0
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real)

/-- Product-form residual with the support nondegeneracy discharged from the actual context.

The only remaining fields are the genuine I.6S stage map, finite L.4.2 half-decrease,
and the Section 26 support-relative product inequality. -/
structure RunClass5LeafSupportProductCoreResidual (ctx : ActualFailureContext) where
  /-- The I.6S charge/stage map of the class-5 fibre. -/
  stageOf : Nat -> Nat
  /-- The finite L.4.2 mass half-decrease on genuine within-descent steps. -/
  hhalf : forall i, i + 1 < runStageLen ctx stageOf ->
    stageMassOf ctx stageOf (i + 1) <= (1 / 2) * stageMassOf ctx stageOf i
  /-- The support-relative Section 26 product bound. -/
  hproduct :
    erdos260Constants.c0 * ((runBaseFibre ctx stageOf).card : Real) *
        stageMassOf ctx stageOf 0
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real)

namespace RunClass5LeafSupportProductCoreResidual

/-- Add the now-proved actual-context support nondegeneracy field. -/
def toSupportProductResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    RunClass5LeafSupportProductResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  hsupport_nontrivial := Or.inr (actualFailureContext_supportShell_card_pos ctx)
  hproduct := R.hproduct

/-- The generated product residual keeps the actual I.6S stage map. -/
@[simp] theorem toSupportProductResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    R.toSupportProductResidual.stageOf = R.stageOf := rfl

end RunClass5LeafSupportProductCoreResidual

namespace RunClass5LeafSupportResidual

/-- The explicit `rhoL` support residual implies the product-form support bound. -/
theorem hproduct {ctx : ActualFailureContext} (R : RunClass5LeafSupportResidual ctx) :
    erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
        stageMassOf ctx R.stageOf 0
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real) := by
  let N : Real := ((runBaseFibre ctx R.stageOf).card : Real)
  let M : Real := stageMassOf ctx R.stageOf 0
  let S : Real := ((supportShell ctx.d ctx.X).card : Real)
  let A : Real := erdos260Constants.cStar * erdos260Constants.ξ / 12
  have hS : 0 <= S := by
    dsimp [S]
    exact Nat.cast_nonneg _
  have hM : 0 <= M := by
    dsimp [M]
    exact stageMassOf_nonneg ctx R.stageOf 0
  have hsmall_nonneg : 0 <= (erdos260Constants.c0 / R.rhoL) * M :=
    mul_nonneg (div_nonneg erdos260Constants.c0_pos.le R.hrhoL_pos.le) hM
  have hrho_ne : Ne R.rhoL 0 := ne_of_gt R.hrhoL_pos
  calc
    erdos260Constants.c0 * N * M
        = (N * R.rhoL) * ((erdos260Constants.c0 / R.rhoL) * M) := by
          field_simp [hrho_ne]
    _ <= S * ((erdos260Constants.c0 / R.rhoL) * M) :=
          mul_le_mul_of_nonneg_right (by simpa [N, S] using R.hpack) hsmall_nonneg
    _ <= S * A :=
          mul_le_mul_of_nonneg_left (by simpa [A, M] using R.hsmall) hS
    _ = A * S := by ring

/-- The explicit support residual gives the nondegeneracy needed by the product form. -/
theorem hsupport_nontrivial {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportResidual ctx) :
    (runBaseFibre ctx R.stageOf).card = 0 \/
      0 < ((supportShell ctx.d ctx.X).card : Real) := by
  by_cases hN : (runBaseFibre ctx R.stageOf).card = 0
  case pos =>
    exact Or.inl hN
  case neg =>
    right
    have hNposNat : 0 < (runBaseFibre ctx R.stageOf).card := Nat.pos_of_ne_zero hN
    have hNpos : 0 < ((runBaseFibre ctx R.stageOf).card : Real) := by
      exact_mod_cast hNposNat
    exact lt_of_lt_of_le (mul_pos hNpos R.hrhoL_pos) R.hpack

/-- Convert the explicit `rhoL` residual to the sharper product-form residual. -/
def toSupportProductResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportResidual ctx) :
    RunClass5LeafSupportProductResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  hsupport_nontrivial := R.hsupport_nontrivial
  hproduct := R.hproduct

end RunClass5LeafSupportResidual

namespace RunClass5LeafSupportProductResidual

/-- The base-stage mass is zero when the base-stage fibre is empty. -/
private theorem stageMass_zero_of_runBaseFibre_card_zero {ctx : ActualFailureContext}
    {stageOf : Nat -> Nat} (hcard : (runBaseFibre ctx stageOf).card = 0) :
    stageMassOf ctx stageOf 0 = 0 := by
  have hempty : runBaseFibre ctx stageOf = (Finset.empty : Finset Nat) :=
    Finset.card_eq_zero.mp hcard
  unfold runBaseFibre at hempty
  unfold stageMassOf
  rw [hempty]
  exact Finset.sum_empty

/-- Reconstruct a positive `rhoL` from the product-form support residual. -/
def toSupportResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductResidual ctx) :
    RunClass5LeafSupportResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  rhoL :=
    if hN : (runBaseFibre ctx R.stageOf).card = 0 then 1
    else ((supportShell ctx.d ctx.X).card : Real) /
      ((runBaseFibre ctx R.stageOf).card : Real)
  hrhoL_pos := by
    by_cases hN : (runBaseFibre ctx R.stageOf).card = 0
    case pos =>
      simp [hN]
    case neg =>
      have hS : 0 < ((supportShell ctx.d ctx.X).card : Real) := by
        cases R.hsupport_nontrivial with
        | inl hzero => exact False.elim (hN hzero)
        | inr hpos => exact hpos
      have hNposNat : 0 < (runBaseFibre ctx R.stageOf).card := Nat.pos_of_ne_zero hN
      have hNpos : 0 < ((runBaseFibre ctx R.stageOf).card : Real) := by
        exact_mod_cast hNposNat
      simp [hN, div_pos hS hNpos]
  hpack := by
    by_cases hN : (runBaseFibre ctx R.stageOf).card = 0
    case pos =>
      have hS : 0 <= ((supportShell ctx.d ctx.X).card : Real) := Nat.cast_nonneg _
      simp [hN]
    case neg =>
      have hNreal : Ne ((runBaseFibre ctx R.stageOf).card : Real) 0 := by
        exact_mod_cast hN
      have hcalc :
          ((runBaseFibre ctx R.stageOf).card : Real) *
              (((supportShell ctx.d ctx.X).card : Real) /
                ((runBaseFibre ctx R.stageOf).card : Real))
            <= ((supportShell ctx.d ctx.X).card : Real) := by
        calc
          ((runBaseFibre ctx R.stageOf).card : Real) *
              (((supportShell ctx.d ctx.X).card : Real) /
                ((runBaseFibre ctx R.stageOf).card : Real))
              = ((supportShell ctx.d ctx.X).card : Real) := by
                field_simp [hNreal]
          _ <= ((supportShell ctx.d ctx.X).card : Real) := le_rfl
      simpa [hN] using hcalc
  hsmall := by
    let N : Real := ((runBaseFibre ctx R.stageOf).card : Real)
    let M : Real := stageMassOf ctx R.stageOf 0
    let S : Real := ((supportShell ctx.d ctx.X).card : Real)
    let A : Real := erdos260Constants.cStar * erdos260Constants.ξ / 12
    by_cases hN : (runBaseFibre ctx R.stageOf).card = 0
    case pos =>
      have hM0 : stageMassOf ctx R.stageOf 0 = 0 :=
        stageMass_zero_of_runBaseFibre_card_zero hN
      have hA : 0 <= A := by
        dsimp [A]
        exact div_nonneg
          (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
          (by norm_num)
      simpa [hN, hM0, A] using hA
    case neg =>
      have hSpos : 0 < S := by
        dsimp [S]
        cases R.hsupport_nontrivial with
        | inl hzero => exact False.elim (hN hzero)
        | inr hpos => exact hpos
      have hNposNat : 0 < (runBaseFibre ctx R.stageOf).card := Nat.pos_of_ne_zero hN
      have hNpos : 0 < N := by
        dsimp [N]
        exact_mod_cast hNposNat
      have hS_ne : Ne S 0 := ne_of_gt hSpos
      have hN_ne : Ne N 0 := ne_of_gt hNpos
      have hmain : (erdos260Constants.c0 * N * M) / S <= A := by
        rw [div_le_iff₀ hSpos]
        simpa [N, M, S, A] using R.hproduct
      have hcalc : (erdos260Constants.c0 / (S / N)) * M <= A := by
        calc
          (erdos260Constants.c0 / (S / N)) * M
              = (erdos260Constants.c0 * N * M) / S := by
                field_simp [hS_ne, hN_ne]
          _ <= A := hmain
      simpa [hN, N, M, S, A] using hcalc

/-- The reconstructed residual keeps the actual I.6S stage map. -/
@[simp] theorem toSupportResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductResidual ctx) :
    R.toSupportResidual.stageOf = R.stageOf := rfl

end RunClass5LeafSupportProductResidual

/-- Family bridge from the product-form support residual to the existing support residual. -/
def runClass5LeafSupportResidual_ofProductResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafSupportResidual ctx :=
  fun ctx => (R ctx).toSupportResidual

/-- Family bridge from the smaller product-core residual to the product-form residual. -/
def runClass5LeafSupportProductResidual_ofCoreResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductCoreResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafSupportProductResidual ctx :=
  fun ctx => (R ctx).toSupportProductResidual

/-- Family bridge from the smaller product-core residual to the existing support residual. -/
def runClass5LeafSupportResidual_ofProductCoreResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductCoreResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafSupportResidual ctx :=
  runClass5LeafSupportResidual_ofProductResidual
    (runClass5LeafSupportProductResidual_ofCoreResidual R)

/-- Family bridge from the product-form support residual to the sharp leaf residual. -/
def runClass5LeafResidual_ofSupportProductResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafResidual ctx :=
  runClass5LeafResidual_ofSupportResidual
    (runClass5LeafSupportResidual_ofProductResidual R)

/-- Family bridge from the smaller product-core residual to the sharp leaf residual. -/
def runClass5LeafResidual_ofSupportProductCoreResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductCoreResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafResidual ctx :=
  runClass5LeafResidual_ofSupportProductResidual
    (runClass5LeafSupportProductResidual_ofCoreResidual R)

/-- The genuine Run class-5 leaf from the product-form support residual. -/
def runClass5GenuineLeaf_ofSupportProductResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5GenuineLeaf ctx :=
  runLeafFromResidual (runClass5LeafResidual_ofSupportProductResidual R)

/-- The genuine Run class-5 leaf from the smaller product-core residual. -/
def runClass5GenuineLeaf_ofSupportProductCoreResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductCoreResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5GenuineLeaf ctx :=
  runLeafFromResidual (runClass5LeafResidual_ofSupportProductCoreResidual R)

/-- The I.5.2 run floor obtained from the product-form support residual. -/
theorem runClass5SupportProductResidual_runFloor
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductResidual ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  runLeafFromResidual_runFloor (runClass5LeafResidual_ofSupportProductResidual R) ctx

/-- The I.5.2 run floor obtained from the smaller product-core residual. -/
theorem runClass5SupportProductCoreResidual_runFloor
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductCoreResidual ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  runLeafFromResidual_runFloor (runClass5LeafResidual_ofSupportProductCoreResidual R) ctx

/-- Honest status of the product-form closure pass. -/
def runSupportClosureStatus : List String :=
  [ "NOT FULLY CLOSED - no unconditional construction of the genuine I.6S stageOf or finite L.4.2 hhalf is present in the current API.",
    "DISCHARGED - support nondegeneracy: actualFailureContext_supportShell_card_pos proves #supportShell > 0 from the actual carry window richness ctx.n24CarryLocal.hKr.",
    "SHARPENED - rhoL/hrhoL_pos/hpack/hsmall are equivalent to the support-relative product residual; the support nontriviality field is no longer residual in the product-core form.",
    "REMAINING - RunClass5LeafSupportProductCoreResidual: stageOf, finite hhalf, and c0 * #runBaseFibre * stageMassOf(ctx,stageOf,0) <= (cStar*xi/12) * #supportShell.",
    "BRIDGE - runClass5LeafSupportResidual_ofProductCoreResidual reconstructs rhoL honestly as #supportShell/#runBaseFibre when the base fibre is nonempty; downstream leaf and floor follow." ]

theorem runSupportClosureStatus_nonempty : runSupportClosureStatus != [] := by
  simp [runSupportClosureStatus]

/-! ## Axiom-cleanliness audit -/

#print axioms RunClass5LeafSupportResidual.hproduct
#print axioms RunClass5LeafSupportResidual.toSupportProductResidual
#print axioms actualFailureContext_supportShell_card_pos
#print axioms RunClass5LeafSupportProductCoreResidual.toSupportProductResidual
#print axioms RunClass5LeafSupportProductResidual.toSupportResidual
#print axioms runClass5LeafSupportResidual_ofProductResidual
#print axioms runClass5LeafSupportProductResidual_ofCoreResidual
#print axioms runClass5LeafSupportResidual_ofProductCoreResidual
#print axioms runClass5LeafResidual_ofSupportProductResidual
#print axioms runClass5LeafResidual_ofSupportProductCoreResidual
#print axioms runClass5GenuineLeaf_ofSupportProductResidual
#print axioms runClass5GenuineLeaf_ofSupportProductCoreResidual
#print axioms runClass5SupportProductResidual_runFloor
#print axioms runClass5SupportProductCoreResidual_runFloor

end

end Erdos260