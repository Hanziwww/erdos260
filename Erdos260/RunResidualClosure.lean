import Erdos260.RunLeafUnconditional

/-!
# Run residual closure: canonical multiplier reduction

This module is an independent closure pass over the remaining
`RunClass5LeafResidual` atom. It does not close the full atom
unconditionally: the I.6S stage map, finite L.4.2 half-decrease, and
support-relative Section 26 packing/smallness remain genuine analytic inputs.

What it does close is the pointwise multiplier part of the current residual.
For the actual base-stage fibre, every individual window excess is bounded by
the actual base-stage mass `stageMassOf ctx stageOf 0`, since that mass is the
sum of nonnegative window excesses over the fibre. Thus the fields
`mult`, `hmult_nonneg`, and `hpoint` of `RunClass5LeafResidual` need not be
residual data.

The remaining reduced residual is `RunClass5LeafSupportResidual`: the genuine
stage map, finite half-decrease, and the Section 26 support-relative `rhoL`
packing plus K.4 smallness with the canonical multiplier
`stageMassOf ctx stageOf 0`.

No `sorry`, `axiom`, `admit`, `native_decide`, or degenerate witness is used.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Canonical pointwise multiplier for the base-stage fibre.

Every member of the actual base-stage fibre has window excess bounded by the
actual base-stage charged mass, because `stageMassOf ctx stageOf 0` is the sum
of the nonnegative window excesses over that fibre. -/
theorem runBaseFibre_windowExcess_le_stageMass
    (ctx : ActualFailureContext) (stageOf : Nat -> Nat) :
    ∀ k ∈ runBaseFibre ctx stageOf,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        <= stageMassOf ctx stageOf 0 := by
  intro k hk
  simpa [runBaseFibre, stageMassOf] using
    (Finset.single_le_sum
      (s := runBaseFibre ctx stageOf)
      (a := k)
      (f := fun j => windowExcess (hitGap ctx.n24CarryData.a) j ctx.n24CarryData.r
        ctx.n24CarryData.T)
      (fun _j _hj => windowExcess_nonneg _ _ _ _)
      hk)

/-- The smaller Run class-5 support residual.

This is `RunClass5LeafResidual` after discharging its pointwise multiplier
fields by the canonical choice `mult = stageMassOf ctx stageOf 0`.

Remaining genuine data:
* `stageOf`: the I.6S charge/stage map;
* `hhalf`: the finite L.4.2 half-decrease on actual stage masses;
* `rhoL`, `hpack`, `hsmall`: the Section 26 support-relative packing and K.4
  smallness, with the canonical multiplier. -/
structure RunClass5LeafSupportResidual (ctx : ActualFailureContext) where
  /-- The I.6S charge/stage map of the class-5 fibre. -/
  stageOf : Nat -> Nat
  /-- The finite L.4.2 mass half-decrease on the genuine within-descent steps. -/
  hhalf : forall i, i + 1 < runStageLen ctx stageOf ->
    stageMassOf ctx stageOf (i + 1) <= (1 / 2) * stageMassOf ctx stageOf i
  /-- The genuine per-hit dense-marker floor `rho_D L`. -/
  rhoL : Real
  /-- The per-hit floor is positive. -/
  hrhoL_pos : 0 < rhoL
  /-- The I.4.1 dense-marker hit packing for the actual base-stage fibre. -/
  hpack : ((runBaseFibre ctx stageOf).card : Real) * rhoL
    <= ((supportShell ctx.d ctx.X).card : Real)
  /-- K.4 smallness with the canonical base-stage mass as multiplier. -/
  hsmall : (erdos260Constants.c0 / rhoL) * stageMassOf ctx stageOf 0
    <= erdos260Constants.cStar * erdos260Constants.ξ / 12

namespace RunClass5LeafSupportResidual

/-- Convert the smaller support residual to the existing sharp leaf residual. -/
def toLeafResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportResidual ctx) : RunClass5LeafResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  mult := stageMassOf ctx R.stageOf 0
  hmult_nonneg := stageMassOf_nonneg ctx R.stageOf 0
  hpoint := runBaseFibre_windowExcess_le_stageMass ctx R.stageOf
  rhoL := R.rhoL
  hrhoL_pos := R.hrhoL_pos
  hpack := R.hpack
  hsmall := R.hsmall

/-- The generated leaf residual uses the actual base-stage mass as multiplier. -/
@[simp] theorem toLeafResidual_mult {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportResidual ctx) :
    R.toLeafResidual.mult = stageMassOf ctx R.stageOf 0 := rfl

/-- The generated leaf residual keeps the actual I.6S stage map. -/
@[simp] theorem toLeafResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportResidual ctx) :
    R.toLeafResidual.stageOf = R.stageOf := rfl

end RunClass5LeafSupportResidual

/-- Family bridge from the smaller support residual to `RunClass5LeafResidual`. -/
def runClass5LeafResidual_ofSupportResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafResidual ctx :=
  fun ctx => (R ctx).toLeafResidual

/-- The genuine Run class-5 leaf from the smaller support residual. -/
def runClass5GenuineLeaf_ofSupportResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5GenuineLeaf ctx :=
  runLeafFromResidual (runClass5LeafResidual_ofSupportResidual R)

/-- The I.5.2 run floor obtained from the smaller support residual. -/
theorem runClass5SupportResidual_runFloor
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportResidual ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  runLeafFromResidual_runFloor (runClass5LeafResidual_ofSupportResidual R) ctx

/-- Honest status of this closure pass. -/
def runResidualClosureStatus : List String :=
  [ "NOT FULLY CLOSED - no unconditional construction of stageOf, finite hhalf, or the Section 26 support-relative rhoL packing/smallness exists in the current API.",
    "DISCHARGED - mult/hmult_nonneg/hpoint of RunClass5LeafResidual, by the canonical multiplier stageMassOf ctx stageOf 0 and nonnegativity of window excess.",
    "REMAINING - RunClass5LeafSupportResidual: stageOf, finite hhalf, rhoL > 0, #runBaseFibre*rhoL <= #supportShell, and (c0/rhoL)*stageMassOf(ctx,stageOf,0) <= cStar*xi/12.",
    "BRIDGE - runClass5LeafResidual_ofSupportResidual converts the smaller residual to RunClass5LeafResidual; runClass5GenuineLeaf_ofSupportResidual and runClass5SupportResidual_runFloor give the downstream leaf and floor." ]

theorem runResidualClosureStatus_nonempty : runResidualClosureStatus != [] := by
  simp [runResidualClosureStatus]

/-! ## Axiom-cleanliness audit -/

#print axioms runBaseFibre_windowExcess_le_stageMass
#print axioms RunClass5LeafSupportResidual.toLeafResidual
#print axioms runClass5LeafResidual_ofSupportResidual
#print axioms runClass5GenuineLeaf_ofSupportResidual
#print axioms runClass5SupportResidual_runFloor

end

end Erdos260