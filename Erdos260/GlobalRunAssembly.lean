import Mathlib
import Erdos260.GlobalReturnAssembly

/-!
# Global run assembly

This module grounds the Run phase one layer further.  The `RunFactoryData`
trichotomy field is derived from a local L.4.1 split, per-output absorption,
and the L.4.2 period-descent contraction certificate.
-/

namespace Erdos260

open Finset

noncomputable section

/-- L.4.2 one-step period-contraction certificate for genuine run-to-run shortenings. -/
structure RunPeriodContractionData
    (chainWeight : Nat -> Real) (chainRatio : Real) where
  chain_contract :
    forall n : Nat, chainWeight (n + 1) <= chainRatio * chainWeight n
  ratio_le_half : chainRatio <= 1 / 2

/-- L.4.2 direct one-step half-decrease certificate for genuine run shortenings. -/
structure RunPeriodHalfDecreaseData
    (chainWeight : Nat -> Real) where
  chain_half :
    forall n : Nat, chainWeight (n + 1) <= chainWeight n / 2

namespace RunPeriodHalfDecreaseData

/-- Convert direct half-decrease into the older ratio-contraction package. -/
def toContraction
    {chainWeight : Nat -> Real}
    (data : RunPeriodHalfDecreaseData chainWeight) :
    RunPeriodContractionData chainWeight (1 / 2) where
  chain_contract := by
    intro n
    calc
      chainWeight (n + 1) <= chainWeight n / 2 := data.chain_half n
      _ = (1 / 2) * chainWeight n := by ring
  ratio_le_half := le_rfl

end RunPeriodHalfDecreaseData

/-- L.4.2 period-descent data: nonnegative weights plus one-step contraction. -/
structure RunPeriodDescentData
    (chainWeight : Nat -> Real) (chainLength : Nat) (chainRatio : Real) where
  chain_nonneg : forall n : Nat, 0 <= chainWeight n
  contraction : RunPeriodContractionData chainWeight chainRatio

namespace RunPeriodDescentData

/-- Build the L.4.2 period-descent certificate from the manuscript's direct
one-step half-decrease estimate. -/
def ofHalfDecrease
    {chainWeight : Nat -> Real} {chainLength : Nat}
    (chain_nonneg : forall n : Nat, 0 <= chainWeight n)
    (chain_half : forall n : Nat, chainWeight (n + 1) <= chainWeight n / 2) :
    RunPeriodDescentData chainWeight chainLength (1 / 2) where
  chain_nonneg := chain_nonneg
  contraction := {
    chain_contract := by
      intro n
      calc
        chainWeight (n + 1) <= chainWeight n / 2 := chain_half n
        _ = (1 / 2) * chainWeight n := by ring
    ratio_le_half := le_rfl }

/-- Project the manuscript's one-step period-contraction estimate. -/
theorem chain_contract
    {chainWeight : Nat -> Real} {chainLength : Nat} {chainRatio : Real}
    (data : RunPeriodDescentData chainWeight chainLength chainRatio) :
    forall n : Nat, chainWeight (n + 1) <= chainRatio * chainWeight n :=
  data.contraction.chain_contract

/-- Project the manuscript's contraction-ratio comparison. -/
theorem ratio_le_half
    {chainWeight : Nat -> Real} {chainLength : Nat} {chainRatio : Real}
    (data : RunPeriodDescentData chainWeight chainLength chainRatio) :
    chainRatio <= 1 / 2 :=
  data.contraction.ratio_le_half

/-- L.4.2 one-step half decrease derived from the period-support contraction. -/
theorem chain_half
    {chainWeight : Nat -> Real} {chainLength : Nat} {chainRatio : Real}
    (data : RunPeriodDescentData chainWeight chainLength chainRatio) :
    forall n : Nat, chainWeight (n + 1) <= chainWeight n / 2 := by
  intro n
  have hratio :
      chainRatio * chainWeight n <= (1 / 2) * chainWeight n :=
    mul_le_mul_of_nonneg_right data.ratio_le_half (data.chain_nonneg n)
  calc
    chainWeight (n + 1) <= chainRatio * chainWeight n :=
      data.chain_contract n
    _ <= (1 / 2) * chainWeight n := hratio
    _ = chainWeight n / 2 := by ring

/-- L.4.2 half-geometric summability of the period-descent chain. -/
theorem periodChain_le
    {chainWeight : Nat -> Real} {chainLength : Nat} {chainRatio : Real}
    (data : RunPeriodDescentData chainWeight chainLength chainRatio) :
    (∑ i ∈ Finset.range chainLength, chainWeight i) <= 2 * chainWeight 0 :=
  halfGeometricSum_bound chainWeight data.chain_nonneg data.chain_half chainLength

end RunPeriodDescentData

/-- L.4.1 absorption of mean-low Run output into the next Tower slot. -/
structure RunMeanLowAbsorptionData (meanLow nextTower : Real) where
  meanLow_le_tower :
    meanLow <= nextTower

/-- L.4.1 absorption of local-spike Run output into the next Return slot. -/
structure RunLocalSpikeAbsorptionData (localSpike nextReturn : Real) where
  localSpike_le_return :
    localSpike <= nextReturn

/-- L.4.1 absorption of boundary Run output into the next DensePack slot. -/
structure RunBoundaryAbsorptionData (boundary nextDensePack : Real) where
  boundary_le_densePack :
    boundary <= nextDensePack

/-- L.4.1 absorption of the shortened-period chain root into the clean CNL tail. -/
structure RunChainRootAbsorptionData (chainRoot cnlTailBudget : Real) where
  chainRoot_le_tail :
    2 * chainRoot <= cnlTailBudget

/-- L.4.1 absorption certificate for the terminal run outputs. -/
structure RunOutputAbsorptionData
    (meanLow localSpike boundary chainRoot nextTower nextReturn nextDensePack
      cnlTailBudget : Real) where
  meanLow :
    RunMeanLowAbsorptionData meanLow nextTower
  localSpike :
    RunLocalSpikeAbsorptionData localSpike nextReturn
  boundary :
    RunBoundaryAbsorptionData boundary nextDensePack
  chainRoot :
    RunChainRootAbsorptionData chainRoot cnlTailBudget

namespace RunOutputAbsorptionData

/-- L.4.1 absorption of routed run outputs into the four next-layer slots. -/
theorem bound
    {meanLow localSpike boundary chainRoot nextTower nextReturn nextDensePack
      cnlTailBudget : Real}
    (data :
      RunOutputAbsorptionData meanLow localSpike boundary chainRoot nextTower
        nextReturn nextDensePack cnlTailBudget) :
    meanLow + localSpike + boundary + 2 * chainRoot <=
      nextTower + nextReturn + nextDensePack + cnlTailBudget := by
  linarith [data.meanLow.meanLow_le_tower, data.localSpike.localSpike_le_return,
    data.boundary.boundary_le_densePack, data.chainRoot.chainRoot_le_tail]

end RunOutputAbsorptionData

/-- L.4.1 deterministic local trichotomy split before output absorption. -/
structure RunLocalSplitData
    (runMass smallError meanLow localSpike boundary : Real)
    (chainWeight : Nat -> Real) (chainLength : Nat) where
  localSplit :
    runMass <=
      meanLow + localSpike + boundary +
        (∑ i ∈ Finset.range chainLength, chainWeight i) + smallError

/-- L.4.1 deterministic run trichotomy together with next-layer absorption. -/
structure RunTrichotomyAbsorptionData
    (runMass nextTower nextReturn nextDensePack twoNegcY X Ij smallError meanLow
      localSpike boundary : Real)
    (chainWeight : Nat -> Real) (chainLength : Nat) where
  localData :
    RunLocalSplitData runMass smallError meanLow localSpike boundary
      chainWeight chainLength
  absorption :
    RunOutputAbsorptionData meanLow localSpike boundary (chainWeight 0)
      nextTower nextReturn nextDensePack (X * Ij * twoNegcY)

namespace RunTrichotomyAbsorptionData

/-- Project the deterministic L.4.1 local split from the split/absorption package. -/
theorem localSplit
    {runMass nextTower nextReturn nextDensePack twoNegcY X Ij smallError meanLow
      localSpike boundary : Real}
    {chainWeight : Nat -> Real} {chainLength : Nat}
    (data :
      RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary chainWeight
        chainLength) :
    runMass <=
      meanLow + localSpike + boundary +
        (∑ i ∈ Finset.range chainLength, chainWeight i) + smallError :=
  data.localData.localSplit

/-- The absorbed L.4.1 terminal output budget. -/
theorem absorb_bound
    {runMass nextTower nextReturn nextDensePack twoNegcY X Ij smallError meanLow
      localSpike boundary : Real}
    {chainWeight : Nat -> Real} {chainLength : Nat}
    (data :
      RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary chainWeight
        chainLength) :
    meanLow + localSpike + boundary + 2 * chainWeight 0 <=
      nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY :=
  data.absorption.bound

/-- L.4.1--L.4.2 run trichotomy in the exact `RunFactoryData` shape. -/
theorem trichotomy_bound
    {runMass nextTower nextReturn nextDensePack twoNegcY X Ij smallError meanLow
      localSpike boundary : Real}
    {chainWeight : Nat -> Real} {chainLength : Nat}
    (data :
      RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary chainWeight
        chainLength)
    (hperiod :
      (∑ i ∈ Finset.range chainLength, chainWeight i) <= 2 * chainWeight 0) :
    runMass <=
      nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError := by
  linarith [data.localSplit, hperiod, data.absorb_bound]

/-- L.4.1--L.4.2 run trichotomy directly from the manuscript one-step
half-decrease certificate. -/
theorem trichotomy_bound_of_halfDecrease
    {runMass nextTower nextReturn nextDensePack twoNegcY X Ij smallError meanLow
      localSpike boundary : Real}
    {chainWeight : Nat -> Real} {chainLength : Nat}
    (data :
      RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary chainWeight
        chainLength)
    (chain_nonneg : forall n : Nat, 0 <= chainWeight n)
    (chain_half : forall n : Nat, chainWeight (n + 1) <= chainWeight n / 2) :
    runMass <=
      nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError :=
  data.trichotomy_bound
    (halfGeometricSum_bound chainWeight chain_nonneg chain_half chainLength)

end RunTrichotomyAbsorptionData

/-- Proof-v4 Run output package: the deterministic L.4.1 split/absorption data
and the L.4.2 direct half-decrease estimate used to collapse shortening chains. -/
structure RunOutputPackageData
    (runMass nextTower nextReturn nextDensePack twoNegcY X Ij smallError meanLow
      localSpike boundary : Real)
    (chainWeight : Nat -> Real) (chainLength : Nat) where
  trichotomy :
    RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
      twoNegcY X Ij smallError meanLow localSpike boundary chainWeight
      chainLength
  periodHalf :
    RunPeriodHalfDecreaseData chainWeight

/--
Proof-v4 aligned Run local data.

The raw `RunFactoryData.trichotomy` inequality is derived from:

* a local trichotomy certificate splitting the run mass into three terminal
  classes plus a period-chain contribution;
* the L.4.2 contraction certificate for genuine period-descents, deriving the
  half-geometric bound for the period chain;
* separate absorption of the three terminal classes and the doubled chain root
  into the next-layer Tower/Return/DensePack/CNL-tail budget.
-/
structure GroundedRunLocalData (cStar xi X : Real) where
  runMass : Real
  nextTower : Real
  nextReturn : Real
  nextDensePack : Real
  twoNegcY : Real
  Ij : Real
  smallError : Real
  meanLow : Real
  localSpike : Real
  boundary : Real
  chainWeight : Nat -> {x : Real // 0 <= x}
  chainLength : Nat
  runPackage_input :
    RunOutputPackageData runMass nextTower nextReturn nextDensePack
      twoNegcY X Ij smallError meanLow localSpike boundary
      (fun n : Nat => (chainWeight n : Real)) chainLength
  hSmall :
    nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError <=
      cStar * xi * X / 6

/--
L.4.1/L.4.2 run leaf before it is packed as grounded Run local data: the
trichotomy/absorption package and direct half-decrease certificate remain
separate.
-/
structure RunLocalLeafInputData (cStar xi X : Real) where
  runMass : Real
  nextTower : Real
  nextReturn : Real
  nextDensePack : Real
  twoNegcY : Real
  Ij : Real
  smallError : Real
  meanLow : Real
  localSpike : Real
  boundary : Real
  chainWeight : Nat -> {x : Real // 0 <= x}
  chainLength : Nat
  trichotomy :
    RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
      twoNegcY X Ij smallError meanLow localSpike boundary
      (fun n : Nat => (chainWeight n : Real)) chainLength
  periodHalf :
    RunPeriodHalfDecreaseData (fun n : Nat => (chainWeight n : Real))
  hSmall :
    nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError <=
      cStar * xi * X / 6

/-- Proposition I.5.2 final scalar smallness comparison for Run. -/
structure RunSmallnessInputData
    (cStar xi X nextTower nextReturn nextDensePack twoNegcY Ij smallError : Real) where
  hSmall :
    nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError <=
      cStar * xi * X / 6

/--
L.4.1/L.4.2 run leaf with the local trichotomy/absorption package,
period-half certificate, and final scalar smallness comparison kept as
separate proof-v4 inputs.
-/
structure RunSeparatedLocalLeafInputData (cStar xi X : Real) where
  runMass : Real
  nextTower : Real
  nextReturn : Real
  nextDensePack : Real
  twoNegcY : Real
  Ij : Real
  smallError : Real
  meanLow : Real
  localSpike : Real
  boundary : Real
  chainWeight : Nat -> {x : Real // 0 <= x}
  chainLength : Nat
  trichotomy :
    RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
      twoNegcY X Ij smallError meanLow localSpike boundary
      (fun n : Nat => (chainWeight n : Real)) chainLength
  periodHalf :
    RunPeriodHalfDecreaseData (fun n : Nat => (chainWeight n : Real))
  smallness :
    RunSmallnessInputData cStar xi X nextTower nextReturn nextDensePack
      twoNegcY Ij smallError

namespace RunLocalLeafInputData

/-- Pack the separated L.4.1/L.4.2 run leaf as grounded Run local data. -/
def toGroundedRunLocalData
    {cStar xi X : Real}
    (data : RunLocalLeafInputData cStar xi X) :
    GroundedRunLocalData cStar xi X where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  meanLow := data.meanLow
  localSpike := data.localSpike
  boundary := data.boundary
  chainWeight := data.chainWeight
  chainLength := data.chainLength
  runPackage_input := {
    trichotomy := data.trichotomy
    periodHalf := data.periodHalf }
  hSmall := data.hSmall

end RunLocalLeafInputData

namespace RunSeparatedLocalLeafInputData

/-- Bundle the separated L.4.1/L.4.2 Run subcertificates into the existing
local Run leaf. -/
def toRunLocalLeafInputData
    {cStar xi X : Real}
    (data : RunSeparatedLocalLeafInputData cStar xi X) :
    RunLocalLeafInputData cStar xi X where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  meanLow := data.meanLow
  localSpike := data.localSpike
  boundary := data.boundary
  chainWeight := data.chainWeight
  chainLength := data.chainLength
  trichotomy := data.trichotomy
  periodHalf := data.periodHalf
  hSmall := data.smallness.hSmall

/-- Convert the separated L.4 Run leaf to grounded Run local data. -/
def toGroundedRunLocalData
    {cStar xi X : Real}
    (data : RunSeparatedLocalLeafInputData cStar xi X) :
    GroundedRunLocalData cStar xi X :=
  data.toRunLocalLeafInputData.toGroundedRunLocalData

end RunSeparatedLocalLeafInputData

/-- Recover the separated L.4.1/L.4.2 run leaf carried by grounded Run data. -/
def GroundedRunLocalData.toLocalLeafInputData
    {cStar xi X : Real}
    (data : GroundedRunLocalData cStar xi X) :
    RunLocalLeafInputData cStar xi X where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  meanLow := data.meanLow
  localSpike := data.localSpike
  boundary := data.boundary
  chainWeight := data.chainWeight
  chainLength := data.chainLength
  trichotomy := data.runPackage_input.trichotomy
  periodHalf := data.runPackage_input.periodHalf
  hSmall := data.hSmall

/-- The real-valued period chain underlying the nonnegative Run weights. -/
def GroundedRunLocalData.chainWeightReal
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    Nat -> Real :=
  fun n => data.chainWeight n

/-- The current grounded run package uses the direct half-decrease normalization. -/
def GroundedRunLocalData.chainRatio
    {cStar xi X : Real} (_data : GroundedRunLocalData cStar xi X) : Real :=
  1 / 2

/-- L.4.2 nonnegativity of period-chain weights, closed by the weight type. -/
theorem GroundedRunLocalData.chain_nonneg
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    forall n : Nat, 0 <= data.chainWeightReal n := by
  intro n
  exact (data.chainWeight n).property

/-- L.4.1 deterministic run trichotomy plus next-layer absorption, carried in
the proof-v4 split/absorption certificate. -/
def GroundedRunLocalData.trichotomy
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    RunTrichotomyAbsorptionData data.runMass data.nextTower data.nextReturn
      data.nextDensePack data.twoNegcY X data.Ij data.smallError data.meanLow
      data.localSpike data.boundary data.chainWeightReal data.chainLength := by
  simpa [GroundedRunLocalData.chainWeightReal] using
    data.runPackage_input.trichotomy

/-- L.4.2 direct half-decrease certificate projected from the proof-v4 Run package. -/
def GroundedRunLocalData.periodHalf
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    RunPeriodHalfDecreaseData data.chainWeightReal := by
  simpa [GroundedRunLocalData.chainWeightReal] using
    data.runPackage_input.periodHalf

/-- L.4.2 one-step period-contraction certificate for the grounded shortening chain. -/
def GroundedRunLocalData.periodContraction
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    RunPeriodContractionData data.chainWeightReal data.chainRatio := by
  simpa [GroundedRunLocalData.chainWeightReal, GroundedRunLocalData.chainRatio]
    using data.periodHalf.toContraction

/-- L.4.2 period-descent certificate for the grounded shortening chain. -/
def GroundedRunLocalData.periodDescent
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    RunPeriodDescentData data.chainWeightReal data.chainLength data.chainRatio where
  chain_nonneg := data.chain_nonneg
  contraction := data.periodContraction

/-- L.4.2 period-contraction estimate for the grounded shortening chain. -/
theorem GroundedRunLocalData.chain_contract
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    forall n : Nat,
      data.chainWeightReal (n + 1) <= data.chainRatio * data.chainWeightReal n := by
  exact data.periodDescent.chain_contract

/-- L.4.2 grounded contraction ratio is at most one half. -/
theorem GroundedRunLocalData.ratio_le_half
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    data.chainRatio <= 1 / 2 := by
  exact data.periodDescent.ratio_le_half

/-- L.4.2 one-step half decrease for the grounded period-shortening chain. -/
theorem GroundedRunLocalData.chain_half
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    forall n : Nat, data.chainWeightReal (n + 1) <= data.chainWeightReal n / 2 := by
  exact data.periodDescent.chain_half

/-- L.4.1 absorption of the routed run outputs into the four next-layer slots. -/
theorem GroundedRunLocalData.absorb_bound
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    data.meanLow + data.localSpike + data.boundary + 2 * data.chainWeightReal 0 <=
      data.nextTower + data.nextReturn + data.nextDensePack +
        X * data.Ij * data.twoNegcY := by
  exact data.trichotomy.absorb_bound

/-- L.4.2 period-descent summability for the grounded run package. -/
theorem GroundedRunLocalData.periodChain_le
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    (∑ i ∈ Finset.range data.chainLength, data.chainWeightReal i) <=
      2 * data.chainWeightReal 0 :=
  data.periodDescent.periodChain_le

/--
L.4.1--L.4.2 run trichotomy bound in the exact `RunFactoryData` shape.

The local split `hLocalSplit` is the deterministic three-way run trichotomy;
`periodChain_le` is the L.4.2 summability of the shorter-period chain; and
`absorb_bound` routes the three terminal classes plus the chain root into the next
Tower/Return/DensePack/CNL-tail budget.
-/
theorem GroundedRunLocalData.trichotomy_bound
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    data.runMass <=
      data.nextTower + data.nextReturn + data.nextDensePack +
        X * data.Ij * data.twoNegcY + data.smallError := by
  exact data.trichotomy.trichotomy_bound data.periodChain_le

/-- Convert L.4-grounded run data into the existing run factory package. -/
def GroundedRunLocalData.toRunFactoryData
    {cStar xi X : Real}
    (data : GroundedRunLocalData cStar xi X) :
    RunFactoryData cStar xi X where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  trichotomy := data.trichotomy_bound
  hSmall := data.hSmall

/-- Proposition I.5.2 for the current L.4-grounded run package. -/
theorem GroundedRunLocalData.run_bound
    {cStar xi X : Real} (data : GroundedRunLocalData cStar xi X) :
    data.runMass <= cStar * xi * X / 6 :=
  runBound_of_factory data.toRunFactoryData

namespace RunLocalLeafInputData

/-- Proposition I.5.2/L.4 final run bound projected directly from the run leaf. -/
theorem run_bound
    {cStar xi X : Real} (data : RunLocalLeafInputData cStar xi X) :
    data.runMass <= cStar * xi * X / 6 :=
  data.toGroundedRunLocalData.run_bound

end RunLocalLeafInputData

namespace RunSeparatedLocalLeafInputData

/-- Proposition I.5.2/L.4 final run bound projected directly from the
separated run leaf. -/
theorem run_bound
    {cStar xi X : Real} (data : RunSeparatedLocalLeafInputData cStar xi X) :
    data.runMass <= cStar * xi * X / 6 :=
  data.toGroundedRunLocalData.run_bound

end RunSeparatedLocalLeafInputData

/--
Core global assembly where carry, Chernoff, CNL, Return, Run, DensePack, and
high-excess use their current proof-v4 grounded interfaces.
-/
structure GlobalAssemblyCoreGroundedCarryChernoffCNLReturnRunDensePackHighExcessInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases ((carry shell hcQ).toCarryData)

/-- Convert the grounded interface with L.4-run data to per-failure assembly. -/
def GlobalAssemblyCoreGroundedCarryChernoffCNLReturnRunDensePackHighExcessInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreGroundedCarryChernoffCNLReturnRunDensePackHighExcessInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d hQ hd hnonterm hrational
    exact (canonicalThresholds Q d hQ hd hnonterm hrational).startThreshold
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic _hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := data.tower shell hcQ
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData)
        ((data.highExcess shell hcQ phases).toHighExcessChargeData)

/--
Erdos 260 from the core interface whose carry, Chernoff, CNL, Return OLC, Run
period chain, DensePack, and high-excess packages are supplied through proof-v4
aligned constructors.
-/
theorem erdos260_final_core_grounded_carry_chernoff_cnl_return_run_densePack_highExcess
    (data :
      GlobalAssemblyCoreGroundedCarryChernoffCNLReturnRunDensePackHighExcessInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

end

end Erdos260
